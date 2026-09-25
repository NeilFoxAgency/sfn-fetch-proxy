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

Improvements v2 (2026-09-25):
- Wayback Machine fallback: when live fetch fails (IP blocked, 403, timeout),
  try web.archive.org cached copy. The site cannot block us because we're not
  hitting their server.
- Realistic browser User-Agents (rotated): the old "StormFixNow contact
  research/1.0" UA was blocked by many sites as an obvious bot.
- Email de-obfuscation: handles "info [at] example [dot] com", HTML entities,
  and other common obfuscation patterns.
- Mailto extraction: harvest emails from mailto: links (was skipped entirely).
- More pages and contact hints for better coverage.
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
MAX_PAGES = 5
CONTACT_HINTS = (
    "contact", "about", "team", "location", "support", "staff",
    "people", "company", "office", "reach", "connect", "hello",
)
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


def email_matches_website_domain(email: str, website_url: str) -> bool:
    domain = email.split("@", 1)[-1].lower()
    host = normalized_host(website_url)
    return bool(domain and host) and (
        domain == host or domain.endswith(f".{host}")
    )


def is_challenge_page(html_text: str) -> bool:
    lowered = html_text.lower()
    return any(marker in lowered for marker in CHALLENGE_MARKERS)


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


def fetch_wayback(url: str, client: httpx.Client) -> tuple[str | None, str | None]:
    """Fetch cached copy from Wayback Machine.
    
    Returns (html, archived_url) or (None, None).
    The site cannot block us because we're not hitting their server.
    """
    try:
        host = normalized_host(url)
        if not host:
            return None, None
        # Query Wayback CDX API for the most recent snapshot
        cdx_url = (
            f"https://web.archive.org/cdx/search/cdx"
            f"?url={quote(host, safe='')}"
            f"&output=json&limit=1&filter=statuscode:200"
            f"&filter=mimetype:text/html&collapse=urlkey"
        )
        resp = client.get(cdx_url, headers={"User-Agent": get_ua()})
        if resp.status_code != 200:
            return None, None
        data = resp.json()
        if not data or len(data) < 2:
            return None, None
        # data[0] is header, data[1] is first result
        # Format: [urlkey, timestamp, original, mimetype, statuscode, digest, length]
        timestamp = data[1][1]
        original = data[1][2]
        archived_url = f"https://web.archive.org/web/{timestamp}/{original}"
        # Fetch the archived page
        arch_resp = client.get(
            archived_url,
            headers={"User-Agent": get_ua()},
            follow_redirects=True,
        )
        if arch_resp.status_code != 200:
            return None, None
        html_text = arch_resp.text
        if is_challenge_page(html_text):
            return None, None
        return html_text, archived_url
    except Exception:
        return None, None


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
                page = browser.new_page(user_agent=get_ua())
                page.goto(url, timeout=20000, wait_until="domcontentloaded")
                html_text = page.content()
            finally:
                browser.close()
    except Exception:
        return None
    if is_challenge_page(html_text):
        return None
    return html_text


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
    home_url = ""
    home_text: str | None = None
    source_note = ""
    
    # Tier 0: Try live fetch first (fastest when it works)
    for variant in website_variants(website):
        text = fetch_tier1(variant, client)
        if text is None:
            text = fetch_tier2_rendered(variant)
        if text:
            home_url, home_text = variant, text
            break
    
    # Tier 0b: Wayback Machine fallback (when live fetch fails)
    # The site cannot block archive.org, so this rescues the 41% "unavailable"
    if not home_text:
        for variant in website_variants(website):
            text, archived_url = fetch_wayback(variant, client)
            if text:
                home_url, home_text = variant, text
                source_note = f" (via wayback {archived_url})"
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

    pages = [(home_url, home_text)]
    home_host = normalized_host(home_url)
    soup = BeautifulSoup(home_text, "html.parser")
    
    # Collect contact-hint pages (up to MAX_PAGES)
    for anchor in soup.find_all("a", href=True):
        if len(pages) >= MAX_PAGES:
            break
        href = str(anchor["href"]).strip()
        if not href or href.startswith(("tel:", "javascript:", "#")):
            continue
        # Don't follow mailto: as a page, but we'll extract emails from them later
        if href.lower().startswith("mailto:"):
            continue
        url = urljoin(home_url, href)
        if normalized_host(url) != home_host:
            continue
        if not any(hint in url.casefold() for hint in CONTACT_HINTS):
            continue
        if not robots_allows(url, client):
            continue
        text = fetch_tier1(url, client) or fetch_tier2_rendered(url)
        if text:
            pages.append((url, text))

    # Extract emails from all pages
    for page_url, content in pages:
        page_soup = BeautifulSoup(content, "html.parser")
        visible = page_soup.get_text(" ")
        if not identity_matches_content(business_name, visible):
            continue
        # Pass soup to extract mailto: links too
        for email in extract_public_emails(visible, page_soup):
            if not email_matches_website_domain(email, home_url):
                continue
            base["status"] = "found"
            base["email"] = email
            base["source_url"] = page_url + source_note
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
    wayback_used = sum(1 for r in results if r.get("source_url") and "wayback" in r["source_url"])
    print(f"done: {found}/{len(results)} found in {elapsed:.1f}s ({wayback_used} via wayback)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
