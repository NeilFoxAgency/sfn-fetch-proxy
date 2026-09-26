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

Strategy (v2):
  - Crawl up to MAX_PAGES pages per site (homepage + contact-pattern pages
    discovered via sitemap.xml, homepage nav/footer links, and a small set
    of probed common paths).
  - Extract emails from mailto: links (highest signal), JSON-LD schema.org
    blocks, visible text, and common obfuscations ("info [at] example
    [dot] com").
  - Identity gate is content-based: the business name (or its significant
    tokens) must appear in the site's visible content/title, or the domain
    must contain a name token. The old domain-only hard gate is gone.
  - First-party rule stays hard: a reported email's domain must match the
    website's domain (or a subdomain of it).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
import warnings
from pathlib import Path
from urllib.parse import urljoin, urlparse
from urllib.robotparser import RobotFileParser

import httpx
from bs4 import BeautifulSoup

try:
    from bs4 import XMLParsedAsHTMLWarning
    warnings.filterwarnings("ignore", category=XMLParsedAsHTMLWarning)
except ImportError:
    pass

USER_AGENT = "StormFixNow contact research/1.0"
REQUEST_TIMEOUT = 12.0
MAX_PAGES = 10
# Soft per-target time budget so one slow site cannot eat the whole batch.
TARGET_BUDGET_SECONDS = 150.0

EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")

# URL path patterns that suggest a contact-ish page, with a relevance score.
# Matched case-insensitively against the URL path.
CONTACT_PATH_PATTERNS = (
    ("contact-us", 90),
    ("contactus", 85),
    ("contact", 80),
    ("contacts", 80),
    ("get-in-touch", 85),
    ("getintouch", 80),
    ("reach-us", 80),
    ("reachus", 75),
    ("connect", 60),
    ("inquiries", 75),
    ("inquiry", 75),
    ("about-us", 70),
    ("aboutus", 65),
    ("about", 60),
    ("our-team", 75),
    ("ourteam", 70),
    ("meet-the-team", 70),
    ("team", 65),
    ("staff", 65),
    ("staff-directory", 70),
    ("directory", 55),
    ("leadership", 60),
    ("locations", 70),
    ("location", 70),
    ("visit", 60),
    ("visit-us", 65),
    ("offices", 65),
    ("office", 60),
    ("support", 60),
    ("help", 50),
    ("feedback", 55),
    ("pastor", 60),
    ("pastors", 60),
    ("clergy", 60),
    ("ministries", 55),
    ("ministry", 55),
)

# Ultra-common contact paths to probe directly when link/sitemap discovery
# yields few candidates. Plain public GETs, nothing evasive.
PROBE_PATHS = (
    "/contact",
    "/contact-us",
    "/contactus",
    "/about",
    "/about-us",
)

# Common obfuscations: "info [at] example [dot] com", "info(at)example.com".
OBFUSCATION_RES = (
    (re.compile(r"\s*[\[\(\{]\s*at\s*[\]\)\}]\s*", re.IGNORECASE), "@"),
    (re.compile(r"\s+at\s+", re.IGNORECASE), "@"),
    (re.compile(r"\s*[\[\(\{]\s*dot\s*[\]\)\}]\s*", re.IGNORECASE), "."),
    (re.compile(r"\s+dot\s+", re.IGNORECASE), "."),
)

# Markers that indicate an access-control challenge page. We treat these as
# fetch failures and never attempt to solve or bypass them.
CHALLENGE_FORM_MARKERS = (
    "cf-challenge",
    "__cf_chl_",
)
CHALLENGE_MENTION_MARKERS = (
    "g-recaptcha",
    "recaptcha",
    "turnstile",
    "data-sitekey",
    "just a moment",
    "checking your browser",
    "verify you are human",
    "are you a robot",
)
CHALLENGE_TITLE_RES = (
    re.compile(r"just a moment", re.IGNORECASE),
    re.compile(r"attention required", re.IGNORECASE),
    re.compile(r"verifying (you are|that you are) human", re.IGNORECASE),
    re.compile(r"checking your browser", re.IGNORECASE),
    re.compile(r"are you a robot", re.IGNORECASE),
    re.compile(r"verify you are human", re.IGNORECASE),
    re.compile(r"security check", re.IGNORECASE),
    re.compile(r"ddos protection", re.IGNORECASE),
    re.compile(r"access denied", re.IGNORECASE),
)

NAME_STOPWORDS = {
    "auto", "business", "care", "clinic", "company", "dental", "family",
    "group", "hotel", "inc", "llc", "restaurant", "sales", "services",
    "storage", "the",
}

# Preferred local parts when several first-party candidates exist.
PREFERRED_LOCAL_PARTS = {
    "info", "contact", "hello", "office", "support", "admin",
    "inquiries", "inquiry", "mail", "email", "general",
}


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
        # Try www / non-www alternates, https first then http (some small
        # business sites still serve plain http only).
        for scheme in ("https", "http"):
            for h in (host, host[4:] if host.startswith("www.")
                      else f"www.{host}"):
                url = parsed._replace(scheme=scheme, netloc=h).geturl()
                if url not in variants:
                    variants.append(url)
    return variants


def name_tokens(business_name: str) -> list[str]:
    return [
        t for t in re.findall(r"[a-z0-9]+", business_name.lower())
        if len(t) >= 4 and t not in NAME_STOPWORDS
    ]


def business_name_matches_domain(business_name: str, url: str) -> bool:
    """Weak identity signal: a name token appears inside the domain."""
    host = normalized_host(url)
    if not host:
        return False
    compact_host = host.replace(".", "").replace("-", "")
    return any(token in compact_host for token in name_tokens(business_name))


def identity_matches_content(business_name: str, text: str) -> bool:
    """Primary identity gate: a name token appears in visible page content."""
    tokens = name_tokens(business_name)
    if not tokens:
        return False
    normalized = re.sub(r"[^a-z0-9]+", " ", (text or "").lower())
    return any(
        re.search(rf"(?:^|\s){re.escape(token)}(?:\s|$)", normalized)
        for token in tokens
    )


def site_identity_verified(business_name: str, home_url: str,
                           home_text: str) -> bool:
    """Content-first identity check.

    Passes when the business name (or a significant token) appears in the
    homepage's visible content or <title>, or when the domain contains a
    name token. The old domain-only hard gate is gone; the domain check is
    now just one of several acceptable signals.
    """
    if identity_matches_content(business_name, home_text):
        return True
    try:
        title = BeautifulSoup(home_text, "html.parser").title
        title_text = title.get_text(" ") if title else ""
    except Exception:
        title_text = ""
    if title_text and identity_matches_content(business_name, title_text):
        return True
    return business_name_matches_domain(business_name, home_url)


def extract_public_emails(text: str) -> list[str]:
    seen: list[str] = []
    for raw in EMAIL_RE.findall(text or ""):
        email = raw.strip().strip(".,;:").lower()
        if email and email not in seen and _looks_valid(email):
            seen.append(email)
    return seen


def deobfuscate_text(text: str) -> str:
    """Turn 'info [at] example [dot] com' into 'info@example.com'."""
    out = text or ""
    for pattern, replacement in OBFUSCATION_RES:
        out = pattern.sub(replacement, out)
    return out


def extract_mailto_emails(soup: BeautifulSoup) -> list[str]:
    """Collect every mailto: address. Highest-signal source on most sites."""
    seen: list[str] = []
    for anchor in soup.find_all("a", href=True):
        href = str(anchor["href"]).strip()
        if not href.lower().startswith("mailto:"):
            continue
        addr = href[7:].split("?", 1)[0].strip().lower()
        # Some sites cram several addresses into one mailto:.
        for raw in re.split(r"[;,]", addr):
            email = raw.strip().strip(".,;:")
            if email and email not in seen and _looks_valid(email):
                seen.append(email)
    return seen


def extract_jsonld_emails(soup: BeautifulSoup) -> list[str]:
    """Pull emails from schema.org JSON-LD blocks (contactPoint, etc.)."""
    seen: list[str] = []

    def _walk(node: object) -> None:
        if isinstance(node, dict):
            for key, value in node.items():
                if isinstance(key, str) and key.lower() == "email":
                    vals = value if isinstance(value, list) else [value]
                    for v in vals:
                        if isinstance(v, str):
                            for email in extract_public_emails(v):
                                if email not in seen:
                                    seen.append(email)
                else:
                    _walk(value)
        elif isinstance(node, list):
            for item in node:
                _walk(item)

    for script in soup.find_all("script", type="application/ld+json"):
        raw = script.string or script.get_text()
        if not raw:
            continue
        try:
            _walk(json.loads(raw))
        except Exception:
            continue
    return seen


def _looks_valid(email: str) -> bool:
    if "@" not in email or email.count("@") != 1:
        return False
    local, domain = email.split("@", 1)
    if not local or not domain or "." not in domain:
        return False
    if ".." in email or email.startswith((".", "-")):
        return False
    # Skip obvious non-contact artifacts.
    if local in {"example", "test", "noreply", "no-reply", "donotreply"}:
        return False
    if domain.startswith("example."):
        return False
    return True


def email_matches_website_domain(email: str, website_url: str) -> bool:
    domain = email.split("@", 1)[-1].lower()
    host = normalized_host(website_url)
    return bool(domain and host) and (
        domain == host or domain.endswith(f".{host}")
    )


def is_challenge_page(html: str) -> bool:
    """Detect access-control challenge pages without false positives.

    A page that merely *mentions* recaptcha/turnstile (e.g. it loads the
    script for its own contact form) is NOT a challenge page. We flag a
    page only when it carries Cloudflare challenge-form markers, has a
    challenge-like <title>, or is nearly content-free while mentioning
    challenge markers.
    """
    lowered = (html or "").lower()
    if any(m in lowered for m in CHALLENGE_FORM_MARKERS):
        return True
    try:
        soup = BeautifulSoup(html, "html.parser")
        title = (soup.title.get_text() if soup.title else "").strip()
        visible_len = len(soup.get_text(" ").strip())
    except Exception:
        title, visible_len = "", 0
    if title and any(rx.search(title) for rx in CHALLENGE_TITLE_RES):
        return True
    if visible_len < 800 and any(
            m in lowered for m in CHALLENGE_MENTION_MARKERS):
        return True
    return False


def fetch_tier1(url: str, client: httpx.Client,
                timeout: float = REQUEST_TIMEOUT) -> str | None:
    """Plain HTTP fetch. Returns page text or None on any failure.

    Retries once on transport-level errors (dropped connections, timeouts)
    with the same User-Agent; HTTP error statuses (403/404/...) are never
    retried since they are explicit server decisions. ``timeout`` caps each
    attempt so a trickling connection cannot hang the batch.
    """
    for _attempt in range(2):
        try:
            response = client.get(url, timeout=timeout)
        except httpx.HTTPError:
            continue
        if response.status_code != 200:
            return None
        try:
            text = response.text
        except Exception:
            return None
        if is_challenge_page(text):
            return None
        return text
    return None


def fetch_tier2_rendered(url: str) -> str | None:
    """Headless-Chromium render for JS-heavy pages. None if unavailable.

    Never used to bypass access controls: challenge pages are detected and
    treated as failures.
    """
    try:
        from playwright.sync_api import sync_playwright
    except ImportError:
        return None
    try:
        with sync_playwright() as playwright:
            browser = playwright.chromium.launch(headless=True)
            try:
                page = browser.new_page(user_agent=USER_AGENT)
                page.goto(url, timeout=20000, wait_until="domcontentloaded")
                html = page.content()
            finally:
                browser.close()
    except Exception:
        return None
    if is_challenge_page(html):
        return None
    return html


def robots_allows(url: str, client: httpx.Client,
                  cache: dict[str, RobotFileParser | None] | None = None
                  ) -> bool:
    """Honor robots.txt, caching one parser per host.

    The cache avoids re-fetching robots.txt for every page of a site (up to
    10 fetches per target without it).
    """
    try:
        parsed = urlparse(url)
        origin = f"{parsed.scheme}://{parsed.netloc}"
        parser: RobotFileParser | None = None
        if cache is not None and origin in cache:
            parser = cache[origin]
        else:
            robots_url = f"{origin}/robots.txt"
            try:
                response = client.get(robots_url)
            except httpx.HTTPError:
                return True
            if response.status_code == 200:
                try:
                    parser = RobotFileParser()
                    parser.set_url(robots_url)
                    parser.parse(response.text.splitlines())
                except Exception:
                    parser = None
            if cache is not None:
                cache[origin] = parser
        if parser is None:
            return True
        return bool(parser.can_fetch(USER_AGENT, url))
    except Exception:
        return True


def sitemap_urls(home_url: str, client: httpx.Client,
                 robots_cache: dict | None = None,
                 timeout: float = 8.0) -> list[str]:
    """Discover same-site page URLs via sitemap.xml / sitemap_index.xml."""
    found: list[str] = []
    parsed = urlparse(home_url)
    base = f"{parsed.scheme}://{parsed.netloc}"
    sitemap_locs = [f"{base}/sitemap.xml", f"{base}/sitemap_index.xml"]

    def _locs(xml_text: str) -> list[str]:
        return re.findall(r"<loc>\s*([^<\s]+)\s*</loc>", xml_text or "",
                          flags=re.IGNORECASE)

    nested: list[str] = []
    for sitemap_url in sitemap_locs:
        if not robots_allows(sitemap_url, client, robots_cache):
            continue
        try:
            text = fetch_tier1(sitemap_url, client, timeout=timeout)
        except Exception:
            text = None
        if not text:
            continue
        for loc in _locs(text):
            if loc.lower().endswith(".xml"):
                if len(nested) < 5:
                    nested.append(loc)
            elif loc not in found:
                found.append(loc)
        if found:
            break
    for nested_url in nested[:5]:
        try:
            text = fetch_tier1(nested_url, client, timeout=timeout)
        except Exception:
            text = None
        for loc in _locs(text or ""):
            if not loc.lower().endswith(".xml") and loc not in found:
                found.append(loc)
    return found


def contact_pattern_score(url: str) -> int:
    """Score a URL by how contact-ish its path looks. 0 = not contact-ish."""
    try:
        path = urlparse(url).path.lower()
    except Exception:
        return 0
    segments = [s for s in path.split("/") if s]
    best = 0
    for pattern, score in CONTACT_PATH_PATTERNS:
        if any(seg == pattern for seg in segments):
            best = max(best, score + 10)  # exact segment match wins
        elif pattern in path:
            best = max(best, score)
    return best


def discover_page_candidates(home_url: str, home_soup: BeautifulSoup,
                             client: httpx.Client,
                             robots_cache: dict | None = None,
                             sitemap_timeout: float | None = 8.0) -> list[str]:
    """Ordered same-host page URLs to crawl (homepage excluded).

    Sources, in priority order: sitemap.xml URLs matching contact patterns,
    homepage links matching contact patterns, a few probed common paths.
    Pass sitemap_timeout=None to skip sitemap discovery (when the time
    budget is nearly exhausted; link parsing is free).
    """
    home_host = normalized_host(home_url)
    scored: dict[str, int] = {}

    def _consider(url: str, score: int) -> None:
        if not url or normalized_host(url) != home_host:
            return
        # Drop non-HTML assets.
        if re.search(r"\.(pdf|jpg|jpeg|png|gif|svg|css|js|zip)(\?|$)",
                     url, re.IGNORECASE):
            return
        key = url.split("#", 1)[0].rstrip("/")
        if key == home_url.rstrip("/"):
            return
        if score > scored.get(key, 0):
            scored[key] = score

    # 1. Sitemap discovery (skipped when the budget is nearly exhausted).
    if sitemap_timeout is not None:
        try:
            for loc in sitemap_urls(home_url, client, robots_cache,
                                    timeout=sitemap_timeout):
                score = contact_pattern_score(loc)
                if score:
                    _consider(loc, score + 5)  # sitemap hits get a small bonus
        except Exception:
            pass

    # 2. Homepage links (nav + footer carry the contact links).
    try:
        for anchor in home_soup.find_all("a", href=True):
            href = str(anchor["href"]).strip()
            if not href or href.startswith(
                    ("mailto:", "tel:", "javascript:", "#")):
                continue
            url = urljoin(home_url, href)
            score = contact_pattern_score(url)
            if score:
                # Links whose anchor text also looks contact-ish rank higher.
                text = (anchor.get_text(" ") or "").lower()
                if any(w in text for w in ("contact", "reach", "touch",
                                          "about", "team", "visit")):
                    score += 10
                _consider(url, score)
    except Exception:
        pass

    # 3. Probe ultra-common paths when discovery came up thin.
    if len(scored) < 3:
        parsed = urlparse(home_url)
        base = f"{parsed.scheme}://{parsed.netloc}"
        for probe in PROBE_PATHS:
            _consider(base + probe, 40)

    ranked = sorted(scored.items(), key=lambda kv: kv[1], reverse=True)
    return [url for url, _ in ranked]


def extract_page_emails(soup: BeautifulSoup,
                        visible_text: str) -> list[tuple[str, int]]:
    """All candidate emails on a page as (email, source_rank) tuples."""
    candidates: list[tuple[str, int]] = []
    seen: set[str] = set()

    def _add(email: str, rank: int) -> None:
        if email not in seen and _looks_valid(email):
            seen.add(email)
            candidates.append((email, rank))

    for email in extract_mailto_emails(soup):
        _add(email, 3)
    for email in extract_jsonld_emails(soup):
        _add(email, 3)
    for email in extract_public_emails(visible_text):
        _add(email, 2)
    for email in extract_public_emails(deobfuscate_text(visible_text)):
        _add(email, 1)
    return candidates


def rank_candidates(candidates: list[tuple[str, str, int]]) -> list[str]:
    """Order (email, page_url, source_rank) by likelihood of being the
    right public contact address. mailto/JSON-LD first, then preferred
    local parts (info@, contact@, ...)."""
    def _key(item: tuple[str, str, int]) -> tuple[int, int, int]:
        email, _, source_rank = item
        local = email.split("@", 1)[0]
        preferred = 1 if local in PREFERRED_LOCAL_PARTS else 0
        return (source_rank, preferred, -len(local))

    ordered = sorted(candidates, key=_key, reverse=True)
    seen: list[str] = []
    for email, _, _ in ordered:
        if email not in seen:
            seen.append(email)
    return seen


def discover_one(
    *,
    business_id: str,
    business_name: str,
    website: str,
    client: httpx.Client,
) -> dict:
    base = {
        "business_id": business_id,
        "business_name": business_name,
        "website": website,
        "status": "not_found",
        "email": None,
        "source_url": None,
        "reason": None,
    }
    deadline = time.time() + TARGET_BUDGET_SECONDS
    robots_cache: dict[str, RobotFileParser | None] = {}

    def _budget_timeout(default: float) -> float | None:
        """Timeout capped at the remaining per-target budget.

        Returns None when the budget is exhausted (caller should stop).
        """
        remaining = deadline - time.time()
        if remaining <= 1.0:
            return None
        return max(2.0, min(default, remaining))

    home_url = ""
    home_text: str | None = None
    for variant in website_variants(website):
        variant_timeout = _budget_timeout(REQUEST_TIMEOUT)
        if variant_timeout is None:
            break
        text = fetch_tier1(variant, client, timeout=variant_timeout)
        if text is None:
            text = fetch_tier2_rendered(variant)
        if text:
            home_url, home_text = variant, text
            break
    if not home_text:
        base["status"] = "error"
        base["reason"] = "website_unavailable"
        return base
    if not robots_allows(home_url, client, robots_cache):
        base["status"] = "error"
        base["reason"] = "robots_disallowed"
        return base
    # Content-first identity gate (domain match is only a weak signal now).
    if not site_identity_verified(business_name, home_url, home_text):
        base["reason"] = "identity_unverified"
        return base

    home_soup = BeautifulSoup(home_text, "html.parser")
    # Sitemap discovery only gets budget-capped time; link parsing is free.
    sitemap_timeout = _budget_timeout(8.0)
    if sitemap_timeout is not None and sitemap_timeout < 4.0:
        sitemap_timeout = None  # too little left; skip sitemap, keep links
    page_urls = [home_url] + discover_page_candidates(
        home_url, home_soup, client, robots_cache,
        sitemap_timeout=sitemap_timeout)[: MAX_PAGES - 1]

    candidates: list[tuple[str, str, int]] = []  # (email, page_url, rank)
    for page_url in page_urls:
        # Cap each fetch at the remaining budget so one trickling
        # connection cannot stall the whole target.
        call_timeout = _budget_timeout(REQUEST_TIMEOUT)
        if call_timeout is None:
            break
        if page_url == home_url:
            content, soup = home_text, home_soup
        else:
            if not robots_allows(page_url, client, robots_cache):
                continue
            content = fetch_tier1(page_url, client, timeout=call_timeout)
            if content is None:
                content = fetch_tier2_rendered(page_url)
            if not content:
                continue
            try:
                soup = BeautifulSoup(content, "html.parser")
            except Exception:
                continue
        try:
            visible = soup.get_text(" ")
        except Exception:
            visible = ""
        # Footer text is a common email hiding spot; weight it by simply
        # including it (it is already part of visible text).
        for email, rank in extract_page_emails(soup, visible):
            if email_matches_website_domain(email, home_url):
                candidates.append((email, page_url, rank))

    for email in rank_candidates(candidates):
        base["status"] = "found"
        base["email"] = email
        # Attribute to the page where this email ranked best.
        for cand_email, page_url, _ in candidates:
            if cand_email == email:
                base["source_url"] = page_url
                break
        return base
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
    with httpx.Client(
        timeout=REQUEST_TIMEOUT,
        headers={"User-Agent": USER_AGENT},
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
                    }
                )
            if index and index % 25 == 0:
                print(f"  ... {index}/{len(targets)} done", flush=True)
    Path(args.out).write_text(json.dumps(results, indent=2))
    elapsed = time.time() - started
    found = sum(1 for r in results if r["status"] == "found")
    print(f"done: {found}/{len(results)} found in {elapsed:.1f}s", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
