#!/usr/bin/env python3
"""
goodreads_ester_mapper.py 🇪🇪📚
Build b-27 • 2025-07-01
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
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Tuple

# ── third-party ──────────────────────────────────────────────────────
import requests
import folium
import html as htm
from bs4 import BeautifulSoup
from geopy.geocoders import Nominatim
from geopy.extra.rate_limiter import RateLimiter
from requests.exceptions import ReadTimeout

# ─── debug helpers ───────────────────────────────────────────────────
DEBUG = bool(int(os.getenv("ESTER_DEBUG", "0")))
CLR = {k: f"\x1b[{v}m" for k, v in dict(dim=90, cyan=36, yel=33,
                                         grn=32, red=31, pur=35, reset=0).items()}
_WHITES = re.compile(r"\s{2,}")
FAILED: List[str] = []

GOODREADS_SHELF = "https://www.goodreads.com/review/list"


def log(tag, msg, col="dim", err=False):
    stream = sys.stderr if err or DEBUG else sys.stdout
    print(f"{CLR[col]}{tag}{CLR['reset']} {msg}", file=stream, flush=True)


def dbg(msg):
    if DEBUG:
        log("•", msg, "red")


try:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

# ─── constants ───────────────────────────────────────────────────────
UA = "goodreads-ester/1.27"
HDRS = {"User-Agent": UA}
TIMEOUT, PAUSE = 30, 1

ESTER = "https://www.ester.ee"
SEARCH = f"{ESTER}/search~S8*est"

GOODREADS_SHELF_URL = "https://www.goodreads.com/review/list"

GEOCACHE = pathlib.Path(".geocache.json")
CITY_BOX = 0.3
CITY_ZOOM = 12
POPUP_CSS = (
    "font-size:1.5em;"
    "max-width:1000px;"
    "max-height:400px;"
    "overflow:auto;"
    "white-space:nowrap;"
)

_DASH = re.compile(r"[\u2010-\u2015\u2212]")
_SLUG = re.compile(r"[^A-Z0-9]")

# ─── static metadata (LIBRARY_META & BRANCH_META) ────────────────────
LIBRARY_META: Dict[str, Tuple[str, str]] = {
    # — national & university level —
    "RaRa": ("Eesti Rahvusraamatukogu", "Tõnismägi 2, Tallinn, Estonia"),
    "TÜR": ("Tartu Ülikooli Raamatukogu", "W. Struve 1, Tartu, Estonia"),
    "TLÜAR": ("Tallinna Ülikooli Akadeemiline RK", "Rävala puiestee 10, Tallinn, Estonia"),
    "TalTech": ("TalTech Raamatukogu (peahoone)", "Akadeemia tee 1, Tallinn, Estonia"),
    "EKA": ("Eesti Kunstiakadeemia Raamatukogu", "Kotzebue 1, Tallinn, Estonia"),
    "EMU": ("Eesti Maaülikooli Raamatukogu", "Fr. R. Kreutzwaldi 1A, Tartu, Estonia"),
    # — public-library systems —
    "TlnRK": ("Tallinna Keskraamatukogu (süsteem)", "Estonia pst 8, Tallinn, Estonia"),
    "Tartu LR": ("Tartu Linnaraamatukogu", "Kompanii 3/5, Tartu, Estonia"),
    # — defence / government —
    "KMAR": ("Kaitseväe Akadeemia Raamatukogu", "Riia 21, Tartu, Estonia"),
    "KV": ("Kaitseväe Peastaabi Raamatukogu", "Juhkentali 58, Tallinn, Estonia"),
    # — small aliases —
    "TARTU": ("Tartu Ülikooli Raamatukogu", "W. Struve 1, Tartu, Estonia"),
    "TLKR": ("Tallinna Keskraamatukogu – Peahoone", "Estonia pst 8, Tallinn, Estonia"),
}

BRANCH_META = {
    "SÜDALINNA": ("TKR Südalinna", "Estonia pst 8, Tallinn"),
    "LIIVALAIA": ("TKR Liivalaia", "Liivalaia 40, Tallinn"),
    "KADRIORU": ("TKR Kadriorg", "Lydia Koidula 12a, Tallinn"),
    "KALAMAJA": ("TKR Kalamaja", "Kotzebue 9, Tallinn"),
    "KÄNNUKUKE": ("TKR Kännukuke", "Eduard Vilde tee 72, Tallinn"),
    "LAAGNA": ("TKR Laagna", "Võru 11, Tallinn"),
    "MÄNNI": ("TKR Männi", "Ehitajate tee 48, Tallinn"),
    "MÄNNIKU": ("TKR Männiku", "Pihlaka 12, Tallinn"),
    "NURMENUKU": ("TKR Nurmenuku", "Ehitajate tee 109a/2, Tallinn"),
    "NÕMME": ("TKR Nõmme", "Raudtee 68, Tallinn"),
    "PAEPEALSE": ("TKR Paepealse", "Paul Pinna 8, Tallinn"),
    "PELGURANNA": ("TKR Pelguranna", "Kangru 13, Tallinn"),
    "PIRITA": ("TKR Pirita", "Metsavahi tee 19, Tallinn"),
    "PÄÄSKÜLA": ("TKR Pääsküla", "Pärnu mnt 480a, Tallinn"),
    "SÕLE": ("TKR Sõle", "Sõle 47b, Tallinn"),
    "SÄÄSE": ("TKR Sääse", "Sõpruse pst 186, Tallinn"),
    "TONDI": ("TKR Tondi", "Pärnu mnt 125, Tallinn"),
    "TORUPILLI": ("TKR Torupilli", "Gonsiori 36, Tallinn"),
    "VÄIKEÕISMÄE": ("TKR Väike-Õismäe", "Õismäe tee 115a, Tallinn"),
    "BUSSI": ("TKR Raamatukogubuss", "Tallinn, Estonia"),
}

def slugify(s: str) -> str:
    return _SLUG.sub("", unicodedata.normalize("NFKD", s)
                     .encode("ascii", "ignore").decode("ascii").upper())

BRANCH_META = {slugify(k): v for k, v in BRANCH_META.items()}

# ─── misc helpers ────────────────────────────────────────────────────
def norm_dash(s: str) -> str: return _DASH.sub("-", s)
def squeeze(s: str) -> str:   return _WHITES.sub(" ", s)
def strip_parens(t: str) -> str: return re.sub(r"\s*\(.*?\)\s*$", "", t).strip()

def ester_enc(s: str) -> str:
    return "".join(ch if ord(ch) < 128 else f"{{u{ord(ch):04X}}}" for ch in s)

def strip_ctrl(t: str) -> str:
    return "".join(ch for ch in t
                   if unicodedata.category(ch)[0] != "C"
                   and unicodedata.category(ch)   != "Cf")

# ─── Goodreads helpers ───────────────────────────────────────────────
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


# ─── Goodreads public-profile scraper  (replaces old gd_scrape) ────
def parse_web_shelf(user_id: str, limit: int | None) -> list[tuple[str,str,str]]:
    """
    Scrape the PUBLIC “to-read” shelf of *user_id* and return a list of
    (author, title, clean_isbn13).  Works with numeric ids OR vanity names.
    """
    out, page = [], 1
    while True:
        url = (f"{GOODREADS_SHELF}/{user_id}"
               f"?shelf=to-read&per_page=200&page={page}"
               f"&sort=date_added&view=table")
        html = _download(url)
        soup = BeautifulSoup(html, "html.parser")

        rows = soup.select("tr[id^='review_']")
        if not rows:                               # empty shelf OR private
            break

        for r in rows:
            a_title  = r.select_one("td.field.title a")
            a_author = r.select_one("td.field.author a")
            td_isbn  = r.select_one("td.field.isbn13")

            title  = a_title .get_text(strip=True) if a_title  else ""
            author = a_author.get_text(strip=True) if a_author else ""

            # clean “isbn139789916711996” → “9789916711996”
            isbn_raw = (td_isbn.get_text(strip=True) if td_isbn else "")
            m = re.search(r"(?i)isbn13\s*:?\s*(\d{13})", isbn_raw)
            isbn13 = m.group(1) if m else ""

            if title and author:
                out.append((author, title, isbn13))
                if limit and len(out) >= limit:
                    return out

        # keep paging while a “next »” link exists
        if soup.select_one("a:-soup-contains('next »')"):
            page += 1
        else:
            break
    return out

def gd_scrape(user: str, limit: int | None):
    """
    Scrape the public ‘to-read’ shelf of any Goodreads profile.
    Works with both the classic *table* view and the newer *card* layout.
    """
    # build base URL from numeric id or full profile link
    if user.isdigit():
        base = f"https://www.goodreads.com/review/list/{user}"
    else:
        m = re.search(r"/user/show/(\d+)", user)
        if not m:
            raise ValueError(
                "--goodreads-user must be a numeric id or a full "
                "profile URL such as https://www.goodreads.com/user/show/1234567-name"
            )
        base = f"https://www.goodreads.com/review/list/{m.group(1)}"

    titles: list[tuple[str, str, str]] = []
    page = 1
    while True:
        # “view=table” forces the old markup if the user allows it;
        # otherwise we’ll fall back to the card parser below.
        url = (f"{base}?shelf=to-read&page={page}"
               f"&per_page=200&sort=date_added&view=table")
        dbg(f"GET {url}")
        r = requests.get(url, headers=HDRS, timeout=TIMEOUT)
        r.raise_for_status()
        soup = BeautifulSoup(r.text, "html.parser")

        # ── ❶ classic table? ───────────────────────────────────────
        rows = soup.select("table#booksBody tr")
        for tr in rows:
            ttl = tr.select_one("td.field.title  a.bookTitle")
            aut = tr.select_one("td.field.author a.authorName")
            if ttl and aut:
                titles.append((aut.get_text(strip=True),
                               ttl.get_text(strip=True),
                               ""))
                if limit and len(titles) >= limit:
                    return titles

        # ── ❷ new card layout? ────────────────────────────────────
        cards = soup.select("div.elementList")
        for card in cards:
            ttl = card.select_one("a.bookTitle")
            aut = card.select_one("a.authorName")
            if ttl and aut:
                titles.append((aut.get_text(strip=True),
                               ttl.get_text(strip=True),
                               ""))
                if limit and len(titles) >= limit:
                    return titles

        # nothing found on this page  → either private or end-of-list
        if not rows and not cards:
            break
        if soup.select_one("a.next_page.disabled"):
            break
        page += 1
        time.sleep(PAUSE)

    return titles

# ─── normalisers used for fuzzy comparisons ─────────────────────────
_norm_re = re.compile(r"[^a-z0-9]+")


def _ascii_fold(s: str) -> str:
    return unicodedata.normalize("NFKD", s).encode("ascii", "ignore") \
                        .decode("ascii").lower()


def _tokenise(s: str) -> set[str]:
    return {tok for tok in _norm_re.split(_ascii_fold(s)) if tok}


def _surname(author: str) -> str:
    """
    Return a lower-case ASCII surname extracted from *author*.

    • when the name is written “Lastname, Firstname …”  → take the
      part before the comma;
    • otherwise fall back to the last word.
    """
    if "," in author:
        before_comma = author.split(",", 1)[0]
        return _ascii_fold(before_comma).split()[0]  # first token
    # old behaviour
    parts = _ascii_fold(author).split()
    return parts[-1] if parts else ""

# ─── ESTER download helpers ─────────────────────────────────────────
SESSION = requests.Session()


def _download(url: str) -> str:
    dbg(f"GET {url}")
    try:
        r = SESSION.get(url, headers=HDRS, timeout=TIMEOUT)
    except ReadTimeout:
        r = SESSION.get(url, headers=HDRS, timeout=TIMEOUT)
    r.raise_for_status()
    return r.text


def _ester_fields(record_url: str) -> tuple[str, str]:
    html = _download(record_url)
    soup = BeautifulSoup(html, "html.parser")

    title_tag = soup.select_one("h1.title, h2.title")
    if not title_tag:
        title_tag = soup.select_one("td#bibTitle")
    if not title_tag:
        title_tag = soup.select_one(
            "td.bibInfoLabel:-soup-contains('Pealkiri') + td.bibInfoData")
    title = strip_ctrl(title_tag.get_text(" ", strip=True)) if title_tag else ""

    auth_tag = soup.select_one(
        "td.bibInfoLabel:-soup-contains('Autor') + td.bibInfoData")
    author = strip_ctrl(auth_tag.get_text(" ", strip=True)) if auth_tag else ""
    return title, author


def _is_eresource(rec_url: str) -> bool:
    """
    Return True when the record is a non-physical e-resource.
    Triggers on any of these keywords, case-insensitive:

        • võrguteavik
        • võrguressurss
        • veebiteavik
        • E-ressursid          (holding location)

    """
    page = _download(rec_url).lower()
    EWORDS = ("võrguteavik", "võrguressurss", "veebiteavik", "e-ressursid")
    return any(w in page for w in EWORDS)

# (some helper functions: _ester_title, _first_candidate_link, collect_record_links
#  keep identical to your last version – omitted here only to save scrolling)

def _first_candidate_link(html: str, base: str) -> str | None:
    soup = BeautifulSoup(html, "html.parser")
    tag = soup.select_one("a[href*='/record=b']")
    if tag:
        return urllib.parse.urljoin(base, tag["href"])
    tag = soup.select_one("h2.title > a[href*='frameset']")
    if tag:
        return urllib.parse.urljoin(base, tag["href"])
    return None


def collect_record_links(url: str) -> list[str]:
    html = _download(url)
    cand = _first_candidate_link(html, url)
    if cand is None:
        return []
    if "frameset" in cand:
        inner_html = _download(cand)
        real = _first_candidate_link(inner_html, cand)
        cand = real or cand
    if _is_eresource(cand):
        soup = BeautifulSoup(html, "html.parser")
        nxt = soup.select("a[href*='/record=b']")
        if len(nxt) > 1:
            cand = urllib.parse.urljoin(url, nxt[1]["href"])
    return [cand]

# ─── sanity check: “is this the same book?” ─────────────────────────
def _looks_like_same_book(want_title: str,
                          want_author: str,
                          record_url: str) -> bool:
    want_title = strip_parens(want_title)
    rec_title, rec_author = _ester_fields(record_url)
    if not rec_title:
        print(f"{want_title!r} — could not extract title → skip")
        return False

    rec_toks = _tokenise(rec_title) | _tokenise(rec_author)
    want_toks = _tokenise(want_title)
    surname = _surname(want_author)

    if surname and surname not in rec_toks:
        print(f"{want_title!r} vs {rec_title!r} → skip "
              f"(surname {surname!r} not found)")
        return False

    overlap = len(want_toks & rec_toks)
    ok = overlap >= max(1, len(want_toks) // 2)
    print(f"{want_title!r} vs {rec_title!r} → "
          f"{'match' if ok else 'skip'} (overlap {overlap}/{len(want_toks)})")
    return ok

# ─── holdings scraper ───────────────────────────────────────────────
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

# ─── location helper -------------------------------------------------
def resolve(loc: str) -> Tuple[str, str]:
    if loc.startswith("TlnRK"):
        rest = loc.removeprefix("TlnRK").lstrip(" ,:-")
        branch_key = slugify(rest.split()[0]) if rest else ""
        if not branch_key:
            return LIBRARY_META["TLKR"]
        return BRANCH_META.get(branch_key,
                               ("Tallinna Keskraamatukogu", "Tallinn"))
    for sigl, (name, addr) in LIBRARY_META.items():
        if loc.startswith(sigl):
            return name, addr
    return loc, ""

# ─── colour helper for marker icons ---------------------------------
def pcol(n: int) -> str:
    if n == 1:
        return "red"
    if n <= 3:
        return "orange"
    if n <= 7:
        return "beige"
    return "green"

# ─── map builder ----------------------------------------------------
def build_map(lib_books, meta, coords, outfile):
    if not coords:
        log("!", "Nothing available (KOHAL) on ESTER", "yel", err=True)
        return

    lats = [la for la, _ in coords.values()]
    lons = [lo for _, lo in coords.values()]
    centre = (sum(lats) / len(lats), sum(lons) / len(lons))

    m = folium.Map(location=centre, zoom_start=11)
    folium.Element("<style>.leaflet-popup-content{max-width:1600px;}</style>").add_to(m)

    for key, books in lib_books.items():
        if key not in coords:
            continue
        lat, lon = coords[key]; name, _ = meta[key]
        html_popup = (f"<div style='{POPUP_CSS}'><b>{htm.escape(name)}</b><ul>"
                      + "".join(f"<li>{htm.escape(b)}</li>" for b in books)
                      + "</ul></div>")
        folium.Marker(
            location=[lat, lon],
            popup=folium.Popup(html_popup, max_width=1600, min_width=300),
            icon=folium.Icon(color=pcol(len(books)), icon="book", prefix="fa"),
        ).add_to(m)

    m.save(outfile)
    log("✓", f"[Done] {outfile}", "grn")

# ─── search helpers (build URLs & probe) ────────────────────────────
def _probe(label: str, url: str) -> list[str]:
    links = collect_record_links(url)
    hits = len(links)
    log("🛰 probe", f"{label:<11} {hits} hit(s)", "grn" if hits else "red")
    if not hits:
        log("⋯", url, "dim")
    return links


def by_isbn(isbn: str) -> list[str]:
    url = (f"{SEARCH}/X?searchtype=X&searcharg={isbn}"
           "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return _probe("keyword-isbn", url)


def by_title_index(title: str) -> list[str]:
    q = ester_enc(norm_dash(title))
    url = (f"{SEARCH}/X?searchtype=t&searcharg="
           f"{urllib.parse.quote_plus(q, safe='{}')}"
           "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return _probe("title-idx", url)


def by_keyword(author: str, title: str) -> list[str]:
    raw = squeeze(f"{author} {title}".strip())
    q = ester_enc(norm_dash(raw))
    url = (f"{SEARCH}/X?searchtype=X&searcharg="
           f"{urllib.parse.quote_plus(q, safe='{}')}"
           "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return _probe("keyword-ttl", url)


def search(author: str, title: str, isbn: str | None) -> list[str]:
    t_clean = strip_parens(title)
    if isbn:
        if (links := by_isbn(isbn)):
            return links
    if (links := by_title_index(t_clean)):
        return links
    if (links := by_keyword(author, t_clean)):
        return links
    return by_keyword("", t_clean)

# ─── per-title worker ------------------------------------------------
def process_title(idx: int, total: int, author: str, title: str, isbn: str):
    t0 = time.time()
    log(f"[{idx:3}/{total}]", f"{author} – {title}", "cyan")
    log("🔖 ISBN:", isbn if isbn else "— none —", "pur")

    local_copies: Counter = Counter()
    local_meta: Dict[str, Tuple[str, str]] = {}

    candidates = search(author, title, isbn)
    first = candidates[0] if candidates else None

    if first and _looks_like_same_book(title, author, first):
        kohals = holdings(first)
        log("📖 ESTER", first, "dim")

        if kohals:
            for loc in kohals:
                name, addr = resolve(loc)
                key = f"{name}|{addr}"
                local_copies[(author, title, key)] += 1
                local_meta[key] = (name, addr)

    total_kohal = sum(local_copies.values())
    if total_kohal:
        log("✓", f"{total_kohal} × KOHAL", "grn")
    else:
        log("✗", "0 × KOHAL", "red")
        FAILED.append(f"{author} – {title}" + (f"  (ISBN {isbn})" if isbn else ""))

    if DEBUG:
        for (a_, t_, key_), n_ in local_copies.items():
            log("DBG-copy", f"{key_:50}  +{n_}", "yel")
    log("⏳", f"{time.time() - t0:.2f}s", "pur")
    return local_copies, local_meta

# ─── geocoder --------------------------------------------------------
def gc_load():
    return json.loads(GEOCACHE.read_text()) if GEOCACHE.exists() else {}


def gc_save(c):
    GEOCACHE.write_text(json.dumps(c, indent=2, ensure_ascii=False))


def geocode(key, addr, geo, cache, force):
    if not addr:
        return None
    if not force and key in cache:
        if DEBUG:
            log("DBG-geo", f"cache {key:<45} → {cache[key]}", "dim")
        return tuple(cache[key])

    loc = geo(addr)
    time.sleep(1)
    if loc:
        cache[key] = (loc.latitude, loc.longitude); gc_save(cache)
        if DEBUG:
            log("DBG-geo", f"fresh {key:<45} → {(loc.latitude, loc.longitude)}", "grn")
        return loc.latitude, loc.longitude

    log("!", f"geocode FAIL {addr}", "red", err=True)
    return None

# ─── main CLI --------------------------------------------------------
def main():
    global DEBUG
    ap = argparse.ArgumentParser()
    gx = ap.add_mutually_exclusive_group(required=True)
    gx.add_argument("--goodreads-csv",  type=pathlib.Path,
                    help="Goodreads export CSV (\"to-read\" shelf)")
    gx.add_argument("--goodreads-user",
                    help="Numeric user-id (or vanity handle) of the PUBLIC Goodreads profile")
    ap.add_argument("--max-titles", type=int, help="Process at most N books")
    ap.add_argument("--geocode",    action="store_true",
                    help="Force fresh geocoding (ignore .geocache)")
    ap.add_argument("--debug",      action="store_true", help="Verbose HTTP/debug output")
    ap.add_argument("--threads",    type=int, default=1, help="Worker threads (default 1)")
    ap.add_argument("--output",     type=pathlib.Path, default="want_to_read_map.html")
    args = ap.parse_args()
    if args.debug:
        DEBUG = True

    # ── load the to-read list ────────────────────────────────────────
    if args.goodreads_csv:
        titles = gd_csv(args.goodreads_csv, args.max_titles)
    else:                         # ONLINE mode (no API key needed)
        titles = parse_web_shelf(args.goodreads_user, args.max_titles)

    log("ℹ", f"{len(titles)} titles", "cyan")

    # ── rest of the pipeline is untouched from your previous file ────
    copies: Counter = Counter(); meta: Dict[str, Tuple[str,str]] = {}

    if args.threads == 1:
        for idx, (a, t, i) in enumerate(titles, 1):
            c, m = process_title(idx, len(titles), a, t, i)
            copies.update(c); meta.update(m)
    else:
        with ThreadPoolExecutor(max_workers=max(1, args.threads)) as pool:
            futs = [pool.submit(process_title, idx, len(titles), a, t, i)
                    for idx, (a, t, i) in enumerate(titles, 1)]
            for f in as_completed(futs):
                c, m = f.result(); copies.update(c); meta.update(m)

    if not copies:
        log("!", "Nothing available (KOHAL) on ESTER", "red", err=True)
        return

    lib_books = defaultdict(list)
    for (au, ti, key), n in copies.items():
        lib_books[key].append(f"{au} – {ti}" + (f" ({n}×)" if n > 1 else ""))

    geo = RateLimiter(Nominatim(user_agent=UA).geocode, min_delay_seconds=1)
    coords = {k: geocode(k, addr, geo, gc_load(), args.geocode)
              for k, (_, addr) in meta.items() if addr}
    coords = {k: v for k, v in coords.items() if v}
    build_map(lib_books, meta, coords, args.output)

    if FAILED:
        log("\n=== TITLES WITH NO *KOHAL* COPIES ===", "", "red")
        for line in FAILED:
            log("✗", line, "red")
        log(f"Total missing: {len(FAILED)}", "", "red")


if __name__ == "__main__":
    main()
