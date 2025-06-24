#!/usr/bin/env python3
"""
goodreads_ester_mapper.py 🇪🇪📚
Build b-26 • 2025-06-29
"""

from __future__ import annotations

# ── stdlib ───────────────────────────────────────────────────────────
import argparse
import csv
import json
import os
import pathlib
import re
import sys
import time
import unicodedata
import urllib.parse
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Tuple

# ── third-party ──────────────────────────────────────────────────────
import requests
from bs4 import BeautifulSoup
from geopy.extra.rate_limiter import RateLimiter
from geopy.geocoders import Nominatim
from requests.exceptions import ReadTimeout
import folium
import html as htm

# ─── debug helpers ───────────────────────────────────────────────────
DEBUG = bool(int(os.getenv("ESTER_DEBUG", "0")))
CLR = {k: f"\x1b[{v}m" for k, v in dict(dim=90, cyan=36,
                                         yel=33, grn=32, red=31,
                                         pur=35, reset=0).items()}
_WHITES = re.compile(r"\s{2,}")
FAILED: List[str] = []

def log(tag, msg, col="dim", err=False):
    stream = sys.stderr if err or DEBUG else sys.stdout
    print(f"{CLR[col]}{tag}{CLR['reset']} {msg}", file=stream, flush=True)

def dbg(msg):       # verbose trace when $ESTER_DEBUG=1
    if DEBUG:
        log("•", msg, "red")

try:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

# ─── constants ───────────────────────────────────────────────────────
UA              = "goodreads-ester/1.26"
HDRS            = {"User-Agent": UA}
TIMEOUT, PAUSE  = 30, 1

GOODREADS_SHELF = "https://www.goodreads.com/review/list"
ESTER           = "https://www.ester.ee"
SEARCH          = f"{ESTER}/search~S8*est"

GEOCACHE  = pathlib.Path(".geocache.json")
CITY_BOX  = 0.3
CITY_ZOOM = 12
POPUP_CSS = "font-size:2em;"

_DASH = re.compile(r"[\u2010-\u2015\u2212]")
_SLUG = re.compile(r"[^A-Z0-9]")

# ─── static metadata (unchanged) ─────────────────────────────────────
LIBRARY_META = {
    "TLÜAR": ("Tallinna Ülikooli Akadeemiline Raamatukogu",
              "Rävala puiestee 10, Tallinn, Estonia"),
    "TLKR":  ("Tallinna Keskraamatukogu – Peahoone",
              "Estonia pst 8, Tallinn, Estonia"),
    "TARTU": ("Tartu Ülikooli Raamatukogu",
              "W. Struve 1, Tartu, Estonia"),
    "EKA":   ("Eesti Kunstiakadeemia Raamatukogu",
              "Kotzebue 1, Tallinn, Estonia"),
    "EMU":   ("Eesti Maaülikooli Raamatukogu",
              "Fr. R. Kreutzwaldi 1A, Tartu, Estonia"),
}

BRANCH_META = {
    "SÜDALINNA":   ("TKR Südalinna",        "Estonia pst 8, Tallinn"),
    "LIIVALAIA":   ("TKR Liivalaia",        "Liivalaia 40, Tallinn"),
    "KADRIORU":    ("TKR Kadriorg",         "Lydia Koidula 12a, Tallinn"),
    "KALAMAJA":    ("TKR Kalamaja",         "Kotzebue 9, Tallinn"),
    "KÄNNUKUKE":   ("TKR Kännukuke",        "Eduard Vilde tee 72, Tallinn"),
    "LAAGNA":      ("TKR Laagna",           "Võru 11, Tallinn"),
    "MÄNNI":       ("TKR Männi",            "Ehitajate tee 48, Tallinn"),
    "MÄNNIKU":     ("TKR Männiku",          "Pihlaka 12, Tallinn"),
    "NURMENUKU":   ("TKR Nurmenuku",        "Ehitajate tee 109a/2, Tallinn"),
    "NÕMME":       ("TKR Nõmme",            "Raudtee 68, Tallinn"),
    "PAEPEALSE":   ("TKR Paepealse",        "Paul Pinna 8, Tallinn"),
    "PELGURANNA":  ("TKR Pelguranna",       "Kangru 13, Tallinn"),
    "PIRITA":      ("TKR Pirita",           "Metsavahi tee 19, Tallinn"),
    "PÄÄSKÜLA":    ("TKR Pääsküla",         "Pärnu mnt 480a, Tallinn"),
    "SÕLE":        ("TKR Sõle",             "Sõle 47b, Tallinn"),
    "SÄÄSE":       ("TKR Sääse",            "Sõpruse pst 186, Tallinn"),
    "TONDI":       ("TKR Tondi",            "Pärnu mnt 125, Tallinn"),
    "TORUPILLI":   ("TKR Torupilli",        "Gonsiori 36, Tallinn"),
    "VÄIKEÕISMÄE": ("TKR Väike-Õismäe",     "Õismäe tee 115a, Tallinn"),
    "BUSSI":       ("TKR Raamatukogubuss",  "Tallinn, Estonia"),
}

def slugify(s: str) -> str:
    return _SLUG.sub("", unicodedata.normalize("NFKD", s)
                     .encode("ascii", "ignore").decode("ascii").upper())

BRANCH_META = {slugify(k): v for k, v in BRANCH_META.items()}

# ─── helpers ─────────────────────────────────────────────────────────
def norm_dash(s: str) -> str: return _DASH.sub("-", s)
def squeeze(s: str) -> str:   return _WHITES.sub(" ", s)
def strip_parens(t: str) -> str: return re.sub(r"\s*\(.*?\)\s*$", "", t).strip()

def ester_enc(s: str) -> str:
    return "".join(ch if ord(ch) < 128 else f"{{u{ord(ch):04X}}}" for ch in s)

def _unwrap_frameset(url: str) -> str:
    """
    If *url* itself is a frameset, fetch it once and return the first
    real /record=b… link found inside.  Otherwise return *url* unchanged.
    """
    if "frameset" not in url:
        return url                       # already a record page
    soup = BeautifulSoup(_download(url), "html.parser")
    rec = soup.select_one("a[href*='/record=b']")
    return urllib.parse.urljoin(url, rec["href"]) if rec else url

def resolve(loc: str) -> Tuple[str, str]:
    if loc.startswith("TlnRK"):
        br = slugify(loc.split(maxsplit=1)[1]) if len(loc.split()) > 1 else ""
        return BRANCH_META.get(br, ("Tallinna Keskraamatukogu", "Tallinn"))
    for cd, (nm, ad) in LIBRARY_META.items():
        if loc.startswith(cd):
            return nm, ad
    return loc, ""

def strip_ctrl(t: str) -> str:
    return "".join(ch for ch in t
                   if unicodedata.category(ch)[0] != "C"
                   and unicodedata.category(ch)   != "Cf")

# ─── HTTP ────────────────────────────────────────────────────────────
SESSION = requests.Session()
def _download(url: str) -> str:
    dbg(f"GET {url}")
    try:
        r = SESSION.get(url, headers=HDRS, timeout=TIMEOUT)
    except ReadTimeout:
        r = SESSION.get(url, headers=HDRS, timeout=TIMEOUT)
    r.raise_for_status()
    return r.text

def _is_eresource(rec_url: str) -> bool:
    """
    Quick test: download the record page once and look for the words that
    ESTER prints for non-physical items.  A page that contains either of
      • '[Võrguteavik]'   (Estonian for “e-resource”)
      • 'E-ressursid'     (holding location for e-files)
    is treated as an e-resource.
    """
    page = _download(rec_url).lower()
    return ("võrguteavik" in page) or ("e-ressursid" in page)

# ─── tiny helper: grab ESTER’s own <h1>/<h2 class="title"> ────────────
def _ester_title(record_url: str) -> str:                    # ★ NEW
    try:
        soup = BeautifulSoup(_download(record_url), "html.parser")
        tag  = soup.select_one("h1.title, h2.title")
        return strip_ctrl(tag.get_text(strip=True)) if tag else record_url
    except Exception:
        return record_url

# ─── universal record-finder (first link only) ───────────────────────
def _extract_record_links(page_html: str) -> list[str]:
    soup = BeautifulSoup(page_html, "html.parser")

    # ❶  Normal case – real record URLs:
    recs = [urllib.parse.urljoin(ESTER, a["href"])
            for a in soup.select("a[href*='/record=b']")]
    if recs:
        return recs

    # ❷  Fallback – search-results pages that point to *framesets*
    #     (first hit is always inside an <h2 class="title"> …):
    fs = [urllib.parse.urljoin(ESTER, a["href"])
          for a in soup.select("h2.title > a[href*='frameset']")]
    return fs          # may be empty – caller will deal with it


def _first_candidate_link(html: str, base: str) -> str | None:
    soup = BeautifulSoup(html, "html.parser")

    # 1) plain record links already in the page
    tag = soup.select_one("a[href*='/record=b']")
    if tag:
        return urllib.parse.urljoin(base, tag["href"])

    # 2) search-result pages: first <h2 class=title> points at a frameset
    tag = soup.select_one("h2.title > a[href*='frameset']")
    if tag:
        return urllib.parse.urljoin(base, tag["href"])

    return None

def collect_record_links(url: str) -> list[str]:
    """
    Return **one** record URL:

    • skip the very first hit *if* it is an e-resource;
    • otherwise just take it and stop – no deep crawling, no loops.
    """
    html = _download(url)
    cand = _first_candidate_link(html, url)
    if cand is None:                       # no hits at all
        return []

    # unwrap the frameset → real /record=b… link
    if "frameset" in cand:
        inner_html = _download(cand)
        real = _first_candidate_link(inner_html, cand)
        cand = real or cand                # fall back if something’s odd

    # if the chosen record is an e-resource, try the next one **once**
    if _is_eresource(cand):
        soup = BeautifulSoup(html, "html.parser")
        nxt = soup.select("a[href*='/record=b']")
        if len(nxt) > 1:
            cand = urllib.parse.urljoin(url, nxt[1]["href"])

    return [cand]

# ─── 2. probe wrapper  (just logging + calling the finder) ───────────
def _probe(label: str, url: str) -> list[str]:
    links = collect_record_links(url)
    hits  = len(links)
    colour = "grn" if hits else "red"
    log("🛰 probe", f"{label:<11} {hits} hit(s)", colour)
    if not hits:
        log("⋯", url, "dim")
    return links


# ─── 3. per-title worker  – use the first link *with* KOHAL ───────────
def process_title(idx: int, total: int, author: str, title: str, isbn: str):
    t0 = time.time()
    log(f"[{idx:3}/{total}]", f"{author} – {title}", "cyan")
    log("🔖 ISBN:", isbn if isbn else "— none —", "pur")

    local_copies: Counter = Counter()
    local_meta: Dict[str, Tuple[str, str]] = {}

    for rec in search(author, title, isbn):
        # we already filtered out e-resources upstream, so just take it
        log("📖 ESTER", rec, "dim")

        kohals = holdings(rec)        # may be an empty list
        for loc in kohals:
            name, addr = resolve(loc)
            key = f"{name}|{addr}"
            local_copies[(author, title, key)] += 1
            local_meta[key] = (name, addr)

        # whatever the KOHAL count is, we stop after the first record
        break

    total_kohal = sum(local_copies.values())
    if total_kohal:
        log("✓", f"{total_kohal} × KOHAL", "grn")
    else:
        log("✗", "0 × KOHAL", "red")
        FAILED.append(f"{author} – {title}"
                      + (f"  (ISBN {isbn})" if isbn else ""))

    log("⏳", f"{time.time() - t0:.2f}s", "pur")
    return local_copies, local_meta

# ─── query builders --------------------------------------------------
def by_isbn(isbn: str) -> list[str]:
    url = (f"{SEARCH}/X?searchtype=X&searcharg={isbn}"
           "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return _probe("keyword-isbn", url)

def by_title_index(title: str) -> list[str]:
    q   = ester_enc(norm_dash(title))
    url = (f"{SEARCH}/X?searchtype=t&searcharg="
           f"{urllib.parse.quote_plus(q, safe='{}')}"
           "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return _probe("title-idx", url)

def by_keyword(author: str, title: str) -> list[str]:
    raw  = squeeze(f"{author} {title}".strip())
    q    = ester_enc(norm_dash(raw))
    url  = (f"{SEARCH}/X?searchtype=X&searcharg="
            f"{urllib.parse.quote_plus(q, safe='{}')}"
            "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return _probe("keyword-ttl", url)

# ─── dispatcher ------------------------------------------------------
def search(author: str, title: str, isbn: str | None) -> list[str]:
    t_clean = strip_parens(title)
    if isbn:
        if (links := by_isbn(isbn)): return links
    if (links := by_title_index(t_clean)): return links
    if (links := by_keyword(author, t_clean)): return links
    return by_keyword("", t_clean)

# ─── holdings scraper ------------------------------------------------
def holdings(record_url: str) -> List[str]:
    m = re.search(r"\b(b\d{7})", record_url)
    if not m:
        return []
    bib = m.group(1)
    full = (f"{ESTER}/search~S8*est?/.{bib}/.{bib}/1,1,1,B/"
            f"holdings~{bib}&FF=&1,0,/indexsort=-")
    soup = BeautifulSoup(_download(full), "html.parser")
    rows = soup.select("#tab-copies tr[class*='bibItemsEntry'], "
                       ".additionalCopies tr[class*='bibItemsEntry']")
    out = []
    for r in rows:
        tds = r.find_all("td")
        if len(tds) < 3:
            continue
        if "KOHAL" not in strip_ctrl(tds[2].get_text()).upper():
            continue
        out.append(strip_ctrl(tds[0].get_text()).strip())
    return out

# ─── Goodreads helpers (unchanged) -----------------------------------
def gd_csv(path: pathlib.Path, limit: int | None):
    out: List[Tuple[str, str, str]] = []
    with path.open(encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            if row.get("Exclusive Shelf", "").lower() != "to-read":
                continue
            author = row["Author"].strip()
            title  = row["Title"].strip()
            isbn   = (row.get("ISBN13") or row.get("ISBN") or "").strip()
            if isbn.startswith('="') and isbn.endswith('"'):
                isbn = isbn[2:-1]
            out.append((author, title, isbn))
            if limit and len(out) >= limit:
                break
    return out

def gd_api(uid, key, limit):
    out, page = [], 1
    while True:
        r = SESSION.get(GOODREADS_SHELF, headers=HDRS, timeout=TIMEOUT,
                        params=dict(v=2, id=uid, key=key, shelf="to-read",
                                    per_page=200, page=page))
        r.raise_for_status()
        reviews = ET.fromstring(r.content).findall("reviews/review")
        if not reviews:
            break
        for rev in reviews:
            b = rev.find("book")
            out.append((b.findtext("authors/author/name", "").strip(),
                        b.findtext("title_without_series", "").strip(),
                        ""))        # v2 feed has no ISBN
            if limit and len(out) >= limit:
                return out
        page += 1
        time.sleep(PAUSE)
    return out

# ─── map helpers (unchanged) -----------------------------------------
def gc_load():
    return json.loads(GEOCACHE.read_text()) if GEOCACHE.exists() else {}
def gc_save(c):
    GEOCACHE.write_text(json.dumps(c, indent=2, ensure_ascii=False))

def geocode(key, addr, geo, cache, force):
    if not addr: return None
    if not force and key in cache: return tuple(cache[key])
    loc = geo(addr); time.sleep(1)
    if loc:
        cache[key] = (loc.latitude, loc.longitude); gc_save(cache)
        return loc.latitude, loc.longitude
    log("!", f"geocode FAIL {addr}", "yel", err=True)
    return None

def pcol(n: int) -> str:
    if n == 1: return "red"
    if n <= 3: return "orange"
    if n <= 7: return "yellow"
    return "green"

def build_map(lib_books, meta, coords, outfile):
    if not coords:
        log("!", "Nothing available (KOHAL) on ESTER", "yel", err=True); return
    lats = [la for la, _ in coords.values()]
    lons = [lo for _, lo in coords.values()]
    zoom = CITY_ZOOM if max(lats)-min(lats) < CITY_BOX and max(lons)-min(lons) < CITY_BOX else 7
    m = folium.Map(location=[sum(lats)/len(lats), sum(lons)/len(lons)], zoom_start=zoom)
    for key, books in lib_books.items():
        if key not in coords: continue
        lat, lon = coords[key]; name, _ = meta[key]
        html_popup = (f"<div style='{POPUP_CSS}'><b>{htm.escape(name)}</b><ul>"
                      + "".join(f"<li>{htm.escape(b)}</li>" for b in books)
                      + "</ul></div>")
        folium.Marker([lat, lon],
                      popup=folium.Popup(html_popup, max_width=350),
                      icon=folium.Icon(color=pcol(len(books)), icon="book", prefix="fa")
                     ).add_to(m)
    m.save(outfile); log("✓", f"[Done] {outfile}", "grn")

# ─── main CLI --------------------------------------------------------
def main():
    global DEBUG
    ap = argparse.ArgumentParser()
    gx = ap.add_mutually_exclusive_group(required=True)
    gx.add_argument("--goodreads-csv", type=pathlib.Path)
    gx.add_argument("--goodreads-user")
    ap.add_argument("--goodreads-key")
    ap.add_argument("--max-titles", type=int)
    ap.add_argument("--geocode", action="store_true")
    ap.add_argument("--debug",   action="store_true")
    ap.add_argument("--threads", type=int, default=1,
                    help="number of worker threads (default 1)")
    ap.add_argument("--output",  type=pathlib.Path,
                    default="want_to_read_map.html")
    args = ap.parse_args()
    if args.debug: DEBUG = True
    if args.goodreads_user and not args.goodreads_key:
        ap.error("--goodreads-key required")

    titles = (gd_csv(args.goodreads_csv, args.max_titles)
              if args.goodreads_csv else
              gd_api(args.goodreads_user, args.goodreads_key, args.max_titles))
    log("ℹ", f"{len(titles)} titles", "cyan")

    copies: Counter = Counter(); meta: Dict[str, Tuple[str, str]] = {}
    if args.threads == 1:
        for idx, (a, t, i) in enumerate(titles, 1):
            c, m = process_title(idx, len(titles), a, t, i)
            copies.update(c); meta.update(m)
    else:
        with ThreadPoolExecutor(max_workers=max(1, args.threads)) as pool:
            fut = [pool.submit(process_title, idx, len(titles), a, t, i13)
                   for idx, (a, t, i13) in enumerate(titles, 1)]
            for f in as_completed(fut):
                c, m = f.result(); copies.update(c); meta.update(m)

    if not copies:
        log("!", "Nothing available (KOHAL) on ESTER", "yel", err=True); return

    lib_books = defaultdict(list)
    for (a, t, key), cnt in copies.items():
        lib_books[key].append(f"{a} – {t}" + (f" ({cnt}×)" if cnt > 1 else ""))

    geo = RateLimiter(Nominatim(user_agent=UA).geocode, min_delay_seconds=1)
    coords = {k: geocode(k, addr, geo, gc_load(), args.geocode)
              for k, (_, addr) in meta.items() if addr}
    coords = {k: c for k, c in coords.items() if c}
    build_map(lib_books, meta, coords, args.output)

    if FAILED:
        log("\n=== TITLES WITH NO *KOHAL* COPIES ===", "", "red")
        for line in FAILED:
            log("✗", line, "red")
        log(f"Total missing: {len(FAILED)}", "", "red")

if __name__ == "__main__":
    main()
