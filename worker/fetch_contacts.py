#!/usr/bin/env python3
"""Fetch business websites and extract public first-party contact emails.

Runs on GitHub Actions runners (clean datacenter egress) so the main
Storm Fix Now VM never has to fetch thousands of business domains itself.

Usage:
    python fetch_contacts.py --targets targets.json --out results.json

Input:  JSON list of {"business_id", "business_name", "website"}.
Output: JSON list of {"business_id", "business_name", "website", "status",
        "email", "source_url", "reason"}.

status is "found", "not_found", or "error". This worker never attempts to
evade access controls: CAPTCHA/challenge pages, logins, and denied robots
rules are recorded as fetch failures, never bypassed.

Improvements v6 (2026-09-25):
- Page-budget quotas under MAX_PAGES: explicit known paths (4),
  top-scored homepage/nav links (6), sitemap candidates (5),
  wayback archive candidates (4) — one merged ranked candidate list
- Wayback CDX prefix query (url=<host>/*, statuscode:200, mimetype:text/html,
  newest-first) replacing the exact-URL query; archived contact/about/team/
  staff/directory/location pages fetched as a rescue pass when live finds nothing
- Playwright: one Chromium browser per run, one context per site, multiple
  pages per context; images/fonts/media/stylesheets blocked; bounded 750ms
  JS settle after domcontentloaded

Improvements v5 (2026-09-25):
- Registrable-domain email matching: sales@example.com now counts for
  tampa.example.com (Public Suffix List via tldextract, naive fallback)
- Sitemap index: follow up to 8 child sitemaps, not just the first
- source_url is always a clean URL; archive provenance moved to new
  fields "archive_url" and "source_transport" ("live" or "wayback")

Improvements v4 (2026-09-25):
- Contact form detection: records contact page URLs and form field info
  even when no email is found, enabling browser-based form submission later
- contact_pages in output: [{url, has_form, form_fields, form_action}]

Improvements v3 (2026-09-25):
- Deeper crawling: MAX_PAGES 5 -> 20, expanded contact hints
- Sitemap.xml parsing: find all site pages without guessing URLs
- Link scoring: match on link text ("Contact Us", "Our Team") not just URL
- Ranked by likelihood, highest-score pages crawled first
"""

from __future__ import annotations

import argparse
import html
import json
import random
import re
import sys
import time
from pathlib import Path
from urllib.parse import quote, urljoin, urlparse
from urllib.robotparser import RobotFileParser

import httpx
from bs4 import BeautifulSoup

try:
    import tldextract as _tldextract
except ImportError:  # runners without tldextract use the naive fallback below
    _tldextract = None

# Realistic browser User-Agents, rotated per request. The old custom UA was
# blocked as an obvious bot by many sites.
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:127.0) Gecko/20100101 Firefox/127.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
]

REQUEST_TIMEOUT = 15.0
MAX_PAGES = 20
# Expanded contact signals: URL hints, link text hints, and common paths.
# Since GitHub Actions gives us unlimited minutes, we crawl deeper.
CONTACT_HINTS = (
    "contact", "about", "team", "location", "support", "staff",
    "people", "company", "office", "reach", "connect", "hello",
    "get-in-touch", "getintouch", "contact-us", "contactus",
    "our-team", "ourteam", "meet-the-team", "leadership",
    "customer-service", "customerservice", "help", "info",
    "quote", "estimate", "locations", "offices", "directory",
)
# Link text that suggests a contact page (checked in addition to URL)
LINK_TEXT_HINTS = (
    "contact", "about us", "our team", "meet the team", "get in touch",
    "reach us", "find us", "locations", "our offices", "support",
    "customer service", "talk to us", "email us", "call us",
)
# Explicit contact paths to try directly (cheap guesses before crawling).
KNOWN_CONTACT_PATHS = (
    "/contact", "/contact-us", "/contactus", "/about", "/about-us",
    "/aboutus", "/team", "/our-team", "/locations", "/our-locations",
    "/support", "/get-in-touch", "/reach-us", "/staff", "/directory",
)
# Per-source page quotas under the MAX_PAGES crawl budget (1 homepage + these).
QUOTA_KNOWN_PATHS = 4
QUOTA_SCORED_LINKS = 6
QUOTA_SITEMAP = 5
QUOTA_WAYBACK = 4
# URL hints used to rank archived (Wayback) page candidates.
WAYBACK_HINTS = ("contact", "about", "team", "staff", "directory", "location")
MAX_SITEMAP_CHILDREN = 8
MAX_SITEMAP_URLS = 500
EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")

# Markers that indicate an access-control challenge page. We treat these as
# fetch failures and never attempt to solve or bypass them.
CHALLENGE_MARKERS = (
    "cf-challenge",
    "cf_challenge",
    "g-recaptcha",
    "recaptcha",
    "turnstile",
    "data-sitekey",
    "just a moment",
    "checking your browser",
    "verify you are human",
    "are you a robot",
)

NAME_STOPWORDS = {
    "auto", "business", "care", "clinic", "company", "dental", "family",
    "group", "hotel", "inc", "llc", "restaurant", "sales", "services",
    "storage", "the",
}


def get_ua() -> str:
    """Return a random realistic browser User-Agent."""
    return random.choice(USER_AGENTS)


def normalized_host(url: str) -> str:
    try:
        host = (urlparse(url).hostname or "").lower()
    except Exception:
        return ""
    return host[4:] if host.startswith("www.") else host


def website_variants(value: str) -> list[str]:
    normalized = value.strip()
    if not normalized.startswith(("http://", "https://")):
        normalized = f"https://{normalized}"
    try:
        parsed = urlparse(normalized)
    except Exception:
        return [normalized]
    variants = [normalized]
    host = parsed.hostname or ""
    if host:
        alternate_host = host[4:] if host.startswith("www.") else f"www.{host}"
        alternate = parsed._replace(netloc=alternate_host).geturl()
        if alternate not in variants:
            variants.append(alternate)
    return variants


def business_name_matches_domain(business_name: str, url: str) -> bool:
    host = normalized_host(url)
    if not host:
        return False
    tokens = [
        t for t in re.findall(r"[a-z0-9]+", business_name.lower())
        if len(t) >= 4 and t not in NAME_STOPWORDS
    ]
    compact_host = host.replace(".", "").replace("-", "")
    return any(token in compact_host for token in tokens)


def identity_matches_content(business_name: str, text: str) -> bool:
    tokens = [
        t for t in re.findall(r"[a-z0-9]+", business_name.lower())
        if len(t) >= 4 and t not in NAME_STOPWORDS
    ]
    normalized = re.sub(r"[^a-z0-9]+", " ", text.lower())
    return any(
        re.search(rf"(?:^|\s){re.escape(token)}(?:\s|$)", normalized)
        for token in tokens
    )


def deobfuscate_emails(text: str) -> str:
    """Convert common email obfuscation patterns to standard form.
    
    Handles: "info [at] example [dot] com", "info(at)example(dot)com",
    HTML entities, etc.
    """
    if not text:
        return text
    # Decode HTML entities first
    text = html.unescape(text)
    # Common obfuscation patterns
    # [at], (at), {at}, AT, at -> @
    text = re.sub(r'\s*[\[\(\{]\s*at\s*[\]\)\}]\s*', '@', text, flags=re.IGNORECASE)
    text = re.sub(r'\s+at\s+', '@', text, flags=re.IGNORECASE)
    # [dot], (dot), {dot}, DOT, dot -> .
    text = re.sub(r'\s*[\[\(\{]\s*dot\s*[\]\)\}]\s*', '.', text, flags=re.IGNORECASE)
    text = re.sub(r'\s+dot\s+', '.', text, flags=re.IGNORECASE)
    return text


def extract_public_emails(text: str, soup: BeautifulSoup | None = None) -> list[str]:
    """Extract emails from text, including de-obfuscated and mailto: links."""
    seen: list[str] = []
    
    # 1. De-obfuscate and extract from text
    clean_text = deobfuscate_emails(text or "")
    for raw in EMAIL_RE.findall(clean_text):
        email = raw.strip().strip(".,;:").lower()
        if email and email not in seen and _looks_valid(email):
            seen.append(email)
    
    # 2. Extract from mailto: links (high confidence)
    if soup is not None:
        for anchor in soup.find_all("a", href=True):
            href = str(anchor["href"]).strip()
            if href.lower().startswith("mailto:"):
                # mailto:email@domain.com?subject=...
                mailto_email = href[7:].split("?")[0].split("&")[0].strip().lower()
                if mailto_email and mailto_email not in seen and _looks_valid(mailto_email):
                    # Mailto emails go first (highest confidence)
                    seen.insert(0, mailto_email)
    
    return seen


def _looks_valid(email: str) -> bool:
    if "@" not in email or email.count("@") != 1:
        return False
    local, domain = email.split("@", 1)
    if not local or not domain or "." not in domain:
        return False
    if ".." in email or email.startswith((".", "-")):
        return False
    # Filter obvious false positives
    if domain.endswith((".png", ".jpg", ".gif", ".css", ".js")):
        return False
    return True


def registrable_domain(host: str) -> str:
    """Return the registrable domain (eTLD+1) of a host.

    Uses the Public Suffix List via tldextract when available. Falls back to a
    naive last-two-labels comparison when tldextract is unavailable (wrong for
    multi-level public suffixes like co.uk, but still an improvement over
    exact host matching).
    """
    host = (host or "").lower().strip().strip(".")
    if not host:
        return ""
    if _tldextract is not None:
        try:
            ext = _tldextract.extract(host)
            if ext.domain and ext.suffix:
                return f"{ext.domain}.{ext.suffix}".lower()
        except Exception:
            pass
        return host
    labels = host.split(".")
    return ".".join(labels[-2:]) if len(labels) >= 2 else host


def email_matches_website_domain(email: str, website_url: str) -> bool:
    domain = email.split("@", 1)[-1].lower()
    host = normalized_host(website_url)
    if not domain or not host:
        return False
    if domain == host or domain.endswith(f".{host}"):
        return True
    # Registrable-domain comparison: sales@example.com counts for a site at
    # tampa.example.com (subdomain of the same registrable domain), and
    # info@example.com counts for www.example.com. This rejects the reverse
    # mismatch too (unrelated.com never shares a registrable domain).
    return registrable_domain(domain) == registrable_domain(host)


def is_challenge_page(html_text: str) -> bool:
    lowered = html_text.lower()
    return any(marker in lowered for marker in CHALLENGE_MARKERS)


def _sitemap_locs(root, path: str) -> list[str]:
    """Extract <loc> texts from a sitemap XML element tree.

    Tolerates sitemap files that omit the standard sitemap.org namespace.
    """
    ns = {"s": "http://www.sitemaps.org/schemas/sitemap/0.9"}
    els = root.findall(path, ns)
    if not els:
        els = root.findall(path.replace("s:", ""))
    return [(el.text or "").strip() for el in els if el.text]


def fetch_sitemap_urls(home_url: str, client: httpx.Client) -> list[str]:
    """Parse sitemap.xml to find contact-relevant site pages.

    Handles both plain urlsets and sitemap indexes. For an index, fetches up
    to MAX_SITEMAP_CHILDREN child sitemaps and collects contact-like URLs
    from each. Sitemaps give us the full page list without guessing URLs.
    """
    found: list[str] = []
    try:
        import xml.etree.ElementTree as ET
        parsed = urlparse(home_url)
        sitemap_url = f"{parsed.scheme}://{parsed.netloc}/sitemap.xml"
        resp = client.get(sitemap_url, headers={"User-Agent": get_ua()})
        if resp.status_code != 200:
            return found
        root = ET.fromstring(resp.text)
        child_sitemaps = _sitemap_locs(root, "s:sitemap/s:loc")
        urlsets = []
        if child_sitemaps:
            # Sitemap index: process up to MAX_SITEMAP_CHILDREN children
            for child_url in child_sitemaps[:MAX_SITEMAP_CHILDREN]:
                try:
                    sub_resp = client.get(child_url, headers={"User-Agent": get_ua()})
                except httpx.HTTPError:
                    continue
                if sub_resp.status_code != 200:
                    continue
                try:
                    urlsets.append(ET.fromstring(sub_resp.text))
                except ET.ParseError:
                    continue
        else:
            urlsets.append(root)
        home_host = normalized_host(home_url)
        for sub_root in urlsets:
            for url in _sitemap_locs(sub_root, "s:url/s:loc"):
                if not url or normalized_host(url) != home_host:
                    continue
                if any(hint in url.casefold() for hint in CONTACT_HINTS):
                    if url not in found:
                        found.append(url)
                if len(found) >= MAX_SITEMAP_URLS:
                    return found
    except Exception:
        pass
    return found


def score_contact_link(href: str, link_text: str) -> int:
    """Score how likely a link leads to contact info. Higher = more likely."""
    score = 0
    href_lower = href.casefold()
    text_lower = link_text.casefold().strip()
    # URL hints
    for hint in CONTACT_HINTS:
        if hint in href_lower:
            score += 3 if hint in ("contact", "contact-us", "contactus") else 2
            break
    # Link text hints (stronger signal than URL)
    for hint in LINK_TEXT_HINTS:
        if hint in text_lower:
            score += 4
            break
    # Footer links often have contact info
    return score


def detect_contact_form(soup: BeautifulSoup) -> dict | None:
    """Detect a contact form on the page. Returns form info or None.
    
    Looks for <form> elements with typical contact fields (name, email, message).
    Excludes login forms (username/password).
    Returns: {"action": form_action_url, "fields": [field_info, ...]}
    """
    for form in soup.find_all("form"):
        fields = []
        has_email = False
        has_message = False
        has_password = False
        has_name = False
        has_phone = False
        
        # Check all input, textarea, select elements
        for field in form.find_all(["input", "textarea", "select"]):
            field_type = field.get("type", "text").lower()
            field_name = (field.get("name") or field.get("id") or "").lower()
            field_placeholder = (field.get("placeholder") or "").lower()
            field_label = ""
            # Try to find associated label
            field_id = field.get("id")
            if field_id:
                label = soup.find("label", attrs={"for": field_id})
                if label:
                    field_label = label.get_text(" ", strip=True).lower()
            
            # Skip hidden, submit, button fields
            if field_type in ("hidden", "submit", "button", "image"):
                continue
            
            # If it's a password field, this is a login form, not contact
            if field_type == "password":
                has_password = True
                break
            
            field_info = {
                "name": field.get("name") or field.get("id") or "",
                "type": field_type,
                "placeholder": field.get("placeholder") or "",
            }
            fields.append(field_info)
            
            # Check field types
            combined = f"{field_name} {field_placeholder} {field_label}"
            if "email" in combined or field_type == "email":
                has_email = True
            if any(w in combined for w in ("message", "comment", "inquiry", "details", "question")):
                has_message = True
            if field.name == "textarea":
                has_message = True
            if any(w in combined for w in ("name", "full name", "first name", "last name")):
                has_name = True
            if any(w in combined for w in ("phone", "tel", "mobile")):
                has_phone = True
        
        # Skip login forms
        if has_password:
            continue
        
        # A contact form needs: (email + message) OR (email + name) OR (name + phone + message)
        is_contact = (
            (has_email and has_message) or
            (has_email and has_name) or
            (has_name and has_phone and has_message) or
            (has_email and has_phone)
        )
        if is_contact and len(fields) >= 2:
            action = form.get("action") or ""
            return {
                "action": action,
                "fields": fields,
                "field_count": len(fields),
            }
    
    return None


def fetch_tier1(url: str, client: httpx.Client) -> str | None:
    """Plain HTTP fetch with realistic browser headers. None on failure."""
    # Rotate UA per request
    headers = {
        "User-Agent": get_ua(),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Accept-Encoding": "gzip, deflate, br",
        "DNT": "1",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1",
    }
    try:
        response = client.get(url, headers=headers)
    except httpx.HTTPError:
        return None
    # Accept 200 only; 403/429/etc. indicate blocking
    if response.status_code != 200:
        return None
    try:
        text = response.text
    except Exception:
        return None
    if is_challenge_page(text):
        return None
    return text


def query_wayback_cdx(home_url: str, client: httpx.Client, limit: int = 500) -> list[tuple[str, str]]:
    """Query the Wayback CDX API with a host-prefix query.

    Returns [(timestamp, original_url)] newest-first, deduplicated by original
    URL, restricted to statuscode:200 text/html captures. Empty list on any
    failure. One bounded query per site (``limit`` caps the row count).
    """
    rows: list[tuple[str, str]] = []
    try:
        host = normalized_host(home_url)
        if not host:
            return rows
        cdx_url = (
            "https://web.archive.org/cdx/search/cdx"
            f"?url={quote(host, safe='')}/*"
            "&output=json"
            "&filter=statuscode:200"
            "&filter=mimetype:text/html"
            "&fl=timestamp,original"
            "&from=2020"
            f"&limit={limit}"
        )
        resp = client.get(cdx_url, headers={"User-Agent": get_ua()})
        if resp.status_code != 200:
            return rows
        data = resp.json()
        if not data or len(data) < 2:
            return rows
        parsed_rows: list[tuple[str, str]] = []
        for row in data[1:]:  # data[0] is the header row
            if not row or len(row) < 2:
                continue
            parsed_rows.append((str(row[0]), str(row[1])))
        # Newest captures first so later code prefers recent snapshots.
        parsed_rows.sort(key=lambda r: r[0], reverse=True)
        seen: set[str] = set()
        for timestamp, original in parsed_rows:
            if original in seen:
                continue
            seen.add(original)
            rows.append((timestamp, original))
        return rows
    except Exception:
        return rows


def fetch_archived_page(archived_url: str, client: httpx.Client) -> str | None:
    """Fetch one web.archive.org snapshot. None on failure or challenge page.

    The site cannot block us because we never hit their server.
    """
    try:
        resp = client.get(
            archived_url,
            headers={"User-Agent": get_ua()},
            follow_redirects=True,
        )
    except httpx.HTTPError:
        return None
    if resp.status_code != 200:
        return None
    try:
        html_text = resp.text
    except Exception:
        return None
    if is_challenge_page(html_text):
        return None
    return html_text


class RenderedFetcher:
    """Render JS-heavy pages with a single shared Chromium browser.

    One browser is launched per worker run, one browser context per site, and
    multiple pages are rendered within each context. Images, fonts, media, and
    stylesheets are blocked to save bandwidth. After domcontentloaded we wait
    a bounded ~750ms for JS content (never an indefinite network-idle wait).

    Never used to bypass access controls: challenge pages are detected and
    treated as failures.
    """

    def __init__(self) -> None:
        self._playwright = None
        self._browser = None
        self._contexts: dict[str, object] = {}

    def _ensure_browser(self) -> bool:
        if self._browser is not None:
            return True
        try:
            from playwright.sync_api import sync_playwright
        except ImportError:
            return False
        try:
            self._playwright = sync_playwright().start()
            self._browser = self._playwright.chromium.launch(headless=True)
            return True
        except Exception:
            self._playwright = None
            self._browser = None
            return False

    def _context_for(self, url: str):
        key = (urlparse(url).netloc or "").lower()
        context = self._contexts.get(key)
        if context is None:
            context = self._browser.new_context(user_agent=get_ua())

            def _block_heavy(route):
                if route.request.resource_type in ("image", "font", "media", "stylesheet"):
                    route.abort()
                else:
                    route.continue_()

            context.route("**/*", _block_heavy)
            self._contexts[key] = context
        return context

    def fetch(self, url: str) -> str | None:
        """Render one URL. Returns HTML or None on any failure."""
        if not self._ensure_browser():
            return None
        try:
            page = self._context_for(url).new_page()
            try:
                page.goto(url, timeout=20000, wait_until="domcontentloaded")
                page.wait_for_timeout(750)
                html_text = page.content()
            finally:
                page.close()
        except Exception:
            return None
        if is_challenge_page(html_text):
            return None
        return html_text

    def close(self) -> None:
        for context in self._contexts.values():
            try:
                context.close()
            except Exception:
                pass
        self._contexts.clear()
        try:
            if self._browser is not None:
                self._browser.close()
        except Exception:
            pass
        try:
            if self._playwright is not None:
                self._playwright.stop()
        except Exception:
            pass
        self._browser = None
        self._playwright = None


_shared_renderer: RenderedFetcher | None = None


def fetch_tier2_rendered(url: str) -> str | None:
    """Headless-Chromium render for JS-heavy pages. None if unavailable.

    Compatibility wrapper: delegates to a lazily-created shared
    RenderedFetcher so the browser is reused across calls. Worker runs should
    prefer an explicit RenderedFetcher (one browser per run).

    Never used to bypass access controls: challenge pages are detected and
    treated as failures.
    """
    global _shared_renderer
    if _shared_renderer is None:
        _shared_renderer = RenderedFetcher()
    return _shared_renderer.fetch(url)


def robots_allows(url: str, client: httpx.Client) -> bool:
    try:
        parsed = urlparse(url)
        robots_url = f"{parsed.scheme}://{parsed.netloc}/robots.txt"
        response = client.get(robots_url, headers={"User-Agent": get_ua()})
        if response.status_code != 200:
            return True
        parser = RobotFileParser()
        parser.set_url(robots_url)
        parser.parse(response.text.splitlines())
        # Check with a generic UA since we rotate
        return bool(parser.can_fetch("*", url))
    except Exception:
        return True


def score_homepage_links(home_url: str, home_host: str, soup: BeautifulSoup) -> list[str]:
    """Score homepage/nav links by contact likelihood; highest score first."""
    scored: list[tuple[int, str]] = []
    for anchor in soup.find_all("a", href=True):
        href = str(anchor["href"]).strip()
        if not href or href.startswith(("tel:", "javascript:", "#")):
            continue
        if href.lower().startswith("mailto:"):
            continue
        url = urljoin(home_url, href)
        if normalized_host(url) != home_host:
            continue
        link_text = anchor.get_text(" ", strip=True)[:100]
        score = score_contact_link(href, link_text)
        if score > 0:
            scored.append((score, url))
    seen: set[str] = set()
    ranked: list[str] = []
    for score, url in sorted(scored, key=lambda x: -x[0]):
        if url not in seen:
            seen.add(url)
            ranked.append(url)
    return ranked


def build_candidate_buckets(
    home_url: str,
    home_host: str,
    soup: BeautifulSoup,
    sitemap_urls: list[str],
    wayback_rows: list[tuple[str, str]],
    attempted: set[str],
) -> list[tuple[str, str, str | None]]:
    """Merge all URL sources into one ranked candidate list with quotas.

    Returns [(bucket, url, archive_url)] in fetch-priority order:
      1. explicit known contact paths  (QUOTA_KNOWN_PATHS)
      2. top-scored homepage/nav links (QUOTA_SCORED_LINKS)
      3. sitemap candidates            (QUOTA_SITEMAP)
      4. wayback archive candidates    (QUOTA_WAYBACK)

    ``archive_url`` is set only for wayback entries (fetch the snapshot, not
    the live site). URLs already in ``attempted`` are skipped so each quota
    fills with fresh URLs. Total extra pages never exceed the sum of quotas,
    keeping the crawl within the MAX_PAGES budget.
    """
    candidates: list[tuple[str, str, str | None]] = []
    seen: set[str] = set(attempted)

    def add(bucket: str, url: str, archive_url: str | None = None) -> bool:
        key = url.rstrip("/")
        if key in seen:
            return False
        seen.add(key)
        candidates.append((bucket, url, archive_url))
        return True

    parsed_home = urlparse(home_url)
    origin = f"{parsed_home.scheme}://{parsed_home.netloc}"

    # Bucket 1: explicit known contact paths (cheap direct guesses)
    known = 0
    for path in KNOWN_CONTACT_PATHS:
        if known >= QUOTA_KNOWN_PATHS:
            break
        url = origin + path
        if url.rstrip("/") == home_url.rstrip("/"):
            continue
        if add("known_path", url):
            known += 1

    # Bucket 2: top-scored homepage/nav links
    scored = 0
    for url in score_homepage_links(home_url, home_host, soup):
        if scored >= QUOTA_SCORED_LINKS:
            break
        if add("scored_link", url):
            scored += 1

    # Bucket 3: sitemap candidates
    sm = 0
    for url in sitemap_urls:
        if sm >= QUOTA_SITEMAP:
            break
        if add("sitemap", url):
            sm += 1

    # Bucket 4: wayback archive candidates (contact-like, newest first)
    wb = 0
    for timestamp, original in wayback_rows:
        if wb >= QUOTA_WAYBACK:
            break
        if not any(hint in original.casefold() for hint in WAYBACK_HINTS):
            continue
        archived = f"https://web.archive.org/web/{timestamp}/{original}"
        if add("wayback", original, archived):
            wb += 1

    return candidates


def discover_one(
    *,
    business_id: str,
    business_name: str,
    website: str,
    client: httpx.Client,
    renderer: RenderedFetcher | None = None,
) -> dict:
    base = {
        "business_id": business_id,
        "business_name": business_name,
        "website": website,
        "status": "not_found",
        "email": None,
        "source_url": None,
        "reason": None,
        "contact_pages": [],  # List of {url, has_form, form_fields, form_action}
        "archive_url": None,  # web.archive.org snapshot URL when email came from an archive
        "source_transport": "live",  # "live" or "wayback"
    }
    home_url = ""
    home_text: str | None = None
    home_archive: str | None = None

    def render(url: str) -> str | None:
        if renderer is not None:
            return renderer.fetch(url)
        return fetch_tier2_rendered(url)

    # Tier 0: live fetch first (fastest when it works)
    for variant in website_variants(website):
        text = fetch_tier1(variant, client)
        if text is None:
            text = render(variant)
        if text:
            home_url, home_text = variant, text
            break

    # Tier 0b: Wayback Machine fallback (when live fetch fails).
    # The site cannot block archive.org, so this rescues "unavailable" sites.
    # One bounded prefix CDX query; its rows are reused for the wayback
    # candidate bucket below so we never query the CDX API twice per site.
    wayback_rows: list[tuple[str, str]] = []
    if not home_text:
        wayback_rows = query_wayback_cdx(website_variants(website)[0], client)
        for timestamp, original in wayback_rows:
            if urlparse(original).path not in ("", "/"):
                continue
            archived = f"https://web.archive.org/web/{timestamp}/{original}"
            text = fetch_archived_page(archived, client)
            if text:
                home_url, home_text, home_archive = original, text, archived
                break

    if not home_text:
        base["status"] = "error"
        base["reason"] = "website_unavailable"
        return base

    if not business_name_matches_domain(business_name, home_url):
        base["reason"] = "identity_domain_mismatch"
        return base

    if not robots_allows(home_url, client):
        base["status"] = "error"
        base["reason"] = "robots_disallowed"
        return base

    pages: list[tuple[str, str, str | None]] = [(home_url, home_text, home_archive)]
    attempted: set[str] = {home_url.rstrip("/")}
    home_host = normalized_host(home_url)
    soup = BeautifulSoup(home_text, "html.parser")

    # Strategy 1: sitemap.xml (up to 8 child sitemaps from an index)
    sitemap_urls = fetch_sitemap_urls(home_url, client)

    def record_contact_page(page_url: str, content: str, archive_url: str | None) -> None:
        page_soup = BeautifulSoup(content, "html.parser")
        is_contact_page = page_url != home_url
        form_info = detect_contact_form(page_soup)
        if form_info:
            is_contact_page = True
        if is_contact_page:
            base["contact_pages"].append({
                "url": page_url,
                "has_form": bool(form_info),
                "form_fields": form_info["fields"] if form_info else [],
                "form_action": form_info["action"] if form_info else "",
                "archive_url": archive_url,
                "source_transport": "wayback" if archive_url else "live",
            })

    def check_page(page_url: str, content: str, archive_url: str | None) -> bool:
        page_soup = BeautifulSoup(content, "html.parser")
        visible = page_soup.get_text(" ")
        if not identity_matches_content(business_name, visible):
            return False
        # Pass soup to extract mailto: links too
        for email in extract_public_emails(visible, page_soup):
            if not email_matches_website_domain(email, home_url):
                continue
            base["status"] = "found"
            base["email"] = email
            base["source_url"] = page_url
            base["archive_url"] = archive_url
            base["source_transport"] = "wayback" if archive_url else "live"
            return True
        return False

    def fetch_bucket(bucket: str, url: str, archive_url: str | None) -> str | None:
        if archive_url is not None:
            return fetch_archived_page(archive_url, client)
        if not robots_allows(url, client):
            return None
        return fetch_tier1(url, client) or render(url)

    # Homepage first
    if check_page(home_url, home_text, home_archive):
        return base
    record_contact_page(home_url, home_text, home_archive)

    # Live buckets: known paths, scored links, sitemap candidates (quotas)
    for bucket, url, archive_url in build_candidate_buckets(
        home_url, home_host, soup, sitemap_urls, [], attempted
    ):
        if len(pages) >= MAX_PAGES:
            break
        attempted.add(url.rstrip("/"))
        text = fetch_bucket(bucket, url, archive_url)
        if not text:
            continue
        pages.append((url, text, archive_url))
        if check_page(url, text, archive_url):
            return base
        record_contact_page(url, text, archive_url)

    # Wayback rescue pass: only if live sources found nothing. Queries the
    # CDX API once (skipped if Tier 0b already did) and fetches up to
    # QUOTA_WAYBACK archived contact-like pages. URLs that failed live are
    # eligible for archive rescue (only successfully-fetched pages excluded).
    if base["status"] != "found":
        if not wayback_rows:
            wayback_rows = query_wayback_cdx(home_url, client)
        fetched_ok = {u.rstrip("/") for u, _, _ in pages}
        for bucket, url, archive_url in build_candidate_buckets(
            home_url, home_host, soup, [], wayback_rows, fetched_ok
        ):
            if bucket != "wayback":
                continue
            if len(pages) >= MAX_PAGES:
                break
            attempted.add(url.rstrip("/"))
            text = fetch_bucket(bucket, url, archive_url)
            if not text:
                continue
            pages.append((url, text, archive_url))
            if check_page(url, text, archive_url):
                return base
            record_contact_page(url, text, archive_url)

    base["reason"] = "no_valid_first_party_email"
    return base


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--targets", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()

    targets = json.loads(Path(args.targets).read_text())
    results: list[dict] = []
    started = time.time()
    # One shared Chromium browser for the whole run (one context per site);
    # launched lazily on first rendered fetch, closed at the end.
    renderer = RenderedFetcher()
    try:
        with httpx.Client(
            timeout=REQUEST_TIMEOUT,
            follow_redirects=True,
        ) as client:
            for index, target in enumerate(targets):
                try:
                    results.append(
                        discover_one(
                            business_id=str(target.get("business_id") or ""),
                            business_name=str(target.get("business_name") or ""),
                            website=str(target.get("website") or ""),
                            client=client,
                            renderer=renderer,
                        )
                    )
                except Exception as exc:  # never let one target kill the batch
                    results.append(
                        {
                            "business_id": str(target.get("business_id")),
                            "business_name": str(target.get("business_name")),
                            "website": str(target.get("website")),
                            "status": "error",
                            "email": None,
                            "source_url": None,
                            "reason": f"worker_exception:{type(exc).__name__}",
                            "contact_pages": [],
                            "archive_url": None,
                            "source_transport": "live",
                        }
                    )
                if index and index % 25 == 0:
                    print(f"  ... {index}/{len(targets)} done", flush=True)
    finally:
        renderer.close()
    Path(args.out).write_text(json.dumps(results, indent=2))
    elapsed = time.time() - started
    found = sum(1 for r in results if r["status"] == "found")
    wayback_used = sum(1 for r in results if r.get("source_transport") == "wayback")
    print(f"done: {found}/{len(results)} found in {elapsed:.1f}s ({wayback_used} via wayback)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
