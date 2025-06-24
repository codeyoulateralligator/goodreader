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
# ── at the top of the file ──────────────────────────
POPUP_CSS = (
    "font-size:1em;"
    "max-width:1000px;"
    "max-height:400px;"
    "overflow:auto;"
    "white-space:nowrap;"
)


_DASH = re.compile(r"[\u2010-\u2015\u2212]")
_SLUG = re.compile(r"[^A-Z0-9]")

# ─── static metadata (unchanged) ─────────────────────────────────────
LIBRARY_META = {
    # — national & university level —
    "RaRa":    ("Eesti Rahvusraamatukogu",              "Tõnismägi 2, Tallinn, Estonia"),
    "TÜR":     ("Tartu Ülikooli Raamatukogu",           "W. Struve 1, Tartu, Estonia"),
    "TLÜAR":   ("Tallinna Ülikooli Akadeemiline RK",    "Rävala puiestee 10, Tallinn, Estonia"),  # you already had this
    "TalTech": ("TalTech Raamatukogu (peahoone)",       "Akadeemia tee 1, Tallinn, Estonia"),
    "EKA":     ("Eesti Kunstiakadeemia Raamatukogu",     "Kotzebue 1, Tallinn, Estonia"),
    "EMU":     ("Eesti Maaülikooli Raamatukogu",        "Fr. R. Kreutzwaldi 1A, Tartu, Estonia"),

    # — public-library systems —
    "TlnRK":   ("Tallinna Keskraamatukogu (süsteem)",   "Estonia pst 8, Tallinn, Estonia"),
    "Tartu LR":("Tartu Linnaraamatukogu",               "Kompanii 3/5, Tartu, Estonia"),

    # — defence / government —
    "KMAR":    ("Kaitseväe Akadeemia Raamatukogu",      "Riia 21, Tartu, Estonia"),
    "KV":      ("Kaitseväe Peastaabi Raamatukogu",      "Juhkentali 58, Tallinn, Estonia"),

    # — smaller but recurring —
    "TARTU":   ("Tartu Ülikooli Raamatukogu (alias)",   "W. Struve 1, Tartu, Estonia"),
    "TLKR":    ("Tallinna Keskraamatukogu – Peahoone",  "Estonia pst 8, Tallinn, Estonia"),      # already in your list
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

def resolve(loc: str) -> tuple[str, str]:
    """
    Map an ESTER holdings location to (nice-name, address).

    • “TlnRK *branch* …”  → use the *first* word after TlnRK
      (“Pirita”, “Kalamaja”, …) and look it up in BRANCH_META.
    • other known SIGL prefixes (RaRa, TÜR …) via LIBRARY_META.
    • everything unknown gets its own marker.
    """
    # —— Tallinna Keskraamatukogu system ———————————————
    if loc.startswith("TlnRK"):
        # strip the prefix and grab just the first word
        rest = loc.removeprefix("TlnRK").lstrip(" ,:-")
        branch_key = slugify(rest.split()[0]) if rest else ""
        if not branch_key:                          # plain “TlnRK”
            return LIBRARY_META["TLKR"]             # Peahoone
        return BRANCH_META.get(branch_key,
                               ("Tallinna Keskraamatukogu", "Tallinn"))

    # —— all other libraries by their SIGL ———————————————
    for sigl, (name, addr) in LIBRARY_META.items():
        if loc.startswith(sigl):
            return name, addr

    # —— totally unknown string ———————————————
    return loc, ""

def _dbg_resolve(raw: str, out: tuple[str, str]) -> None:
    if DEBUG:
        log("DBG-loc", f"{raw!r} → {out!r}", "dim")

def strip_ctrl(t: str) -> str:
    return "".join(ch for ch in t
                   if unicodedata.category(ch)[0] != "C"
                   and unicodedata.category(ch)   != "Cf")

# ─── helpers used for fuzzy comparisons ─────────────────────────────
_norm_re = re.compile(r"[^a-z0-9]+")

def _ascii_fold(s: str) -> str:
    """Unicode → pure ASCII, lower-case."""
    return unicodedata.normalize("NFKD", s).encode("ascii", "ignore") \
                        .decode("ascii").lower()

def _tokenise(s: str) -> set[str]:
    """Return a *set* of alphanumeric tokens (ASCII-folded, lower-case)."""
    return {tok for tok in _norm_re.split(_ascii_fold(s)) if tok}

def _surname(author: str) -> str:
    parts = re.sub(r"[^A-Za-z0-9 ]+", " ",
                   unicodedata.normalize("NFKD", author)
                   .encode("ascii", "ignore").decode("ascii")).lower().split()
    return parts[-1] if parts else ""

def _ester_fields(record_url: str) -> tuple[str, str]:
    """
    Return (title, author_text) extracted from one ESTER record page.
      • *title*   →  the main display title  (Pealkiri  ♦  Ühtluspealkiri)
      • *author*  →  the full author field  (Autor …)

    If parsing fails, either field is returned as "".
    """
    html = _download(record_url)
    soup = BeautifulSoup(html, "html.parser")

    # ❶ MAIN TITLE  (either <h1 class="title"> or the Pealkiri row)
    tag = soup.select_one("h1.title, h2.title")
    if not tag:                                             # fallback
        tag = soup.select_one("td.bibInfoLabel:-soup-contains('Pealkiri') "
                              "+ td.bibInfoData")
    title = strip_ctrl(tag.get_text(" ", strip=True)) if tag else ""

    # ❷ AUTHOR
    tag = soup.select_one("td.bibInfoLabel:-soup-contains('Autor') "
                          "+ td.bibInfoData")
    author = strip_ctrl(tag.get_text(" ", strip=True)) if tag else ""

    return title, author

# ─── quick “is this the same book?” guard  (DEBUG prints kept) ──────
# ─── quick “is this the same book?” guard  (DEBUG prints kept) ──────
def _looks_like_same_book(want_title: str,
                          want_author: str,
                          record_url: str) -> bool:
    """
    True  ⇒ record_url is probably the same book
    False ⇒ skip it

    • author’s **surname** has to appear somewhere in the record
    • ≥ 50 % of wanted-title tokens must overlap with the record title
    """
    # 1) ignore “( … )” trailers such as series info or part numbers
    want_title = strip_parens(want_title)

    # 2) pull both title *and* author line from the ESTER record page
    rec_title, rec_author = _ester_fields(record_url)

    # bail if we could not read anything useful
    if not rec_title:
        print(f"{want_title!r} — could not extract title → skip")
        return False

    # 3) tokenise: ASCII-fold, lower-case, strip punctuation
    rec_toks   = _tokenise(rec_title) | _tokenise(rec_author)
    want_toks  = _tokenise(want_title)
    surname    = _surname(want_author)

    # 4) author surname must be present
    if surname and surname not in rec_toks:
        print(f"{want_title!r} vs {rec_title!r} → skip "
              f"(surname {surname!r} not found)")
        return False

    # 5) at least half the title tokens must overlap
    overlap = len(want_toks & rec_toks)
    ok = overlap >= max(1, len(want_toks) // 2)

    print(f"{want_title!r} vs {rec_title!r} → "
          f"{'match' if ok else 'skip'} (overlap {overlap}/{len(want_toks)})")
    return ok


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
def _ester_title(url: str,
                 *, _seen: set[str] | None = None,
                 _depth: int = 0,
                 _max_depth: int = 4) -> str:
    """
    Return the display title for one `/record=b…` page.

    Works with:
      • the new single-page UI  (has <h1|h2 class="title">)
      • the old MARC view       (title sits in <td id="bibTitle">  *or*
                                 next to label “Pealkiri”)
      • the legacy frameset UI  (title buried in the *second* frame)
    Falls back to the URL if nothing useful can be extracted.
    """
    if _seen is None:
        _seen = set()
    if url in _seen or _depth >= _max_depth:
        return url               # prevent loops

    _seen.add(url)
    try:
        html = _download(url)
    except Exception:
        return url

    soup = BeautifulSoup(html, "html.parser")

    # ❶ modern UI ─────
    tag = soup.select_one("h1.title, h2.title")
    if tag and tag.get_text(strip=True):
        return strip_ctrl(tag.get_text(strip=True))

    # ❷ old MARC view ─
    #    a) direct <td id="bibTitle">
    tag = soup.select_one("td#bibTitle")
    if tag and tag.get_text(strip=True):
        return strip_ctrl(tag.get_text(strip=True))

    #    b) generic two-column layout  (“Pealkiri” / title)
    for row in soup.select("tr"):
        lbl = row.select_one("td.bibInfoLabel")
        dat = row.select_one("td.bibInfoData")
        if lbl and dat and "pealkiri" in lbl.get_text(strip=True).lower():
            txt = dat.get_text(strip=True)
            if txt:
                return strip_ctrl(txt)

    # ❸ frameset ──────
    for fr in soup.find_all(["frame", "iframe"], src=True):
        child = urllib.parse.urljoin(url, fr["src"])
        got = _ester_title(child,
                           _seen=_seen,
                           _depth=_depth + 1,
                           _max_depth=_max_depth)
        if not got.startswith(("http://", "https://")):  # success
            return got

    # ❹ hopeless ──────
    return url

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

    # --- grab ONLY the top-ranked record ---------------------------------
    candidates = search(author, title, isbn)
    first = candidates[0] if candidates else None

    if first and _looks_like_same_book(title, author, first):
        kohals = holdings(first)          # ← fetch once
        log("📖 ESTER", first, "dim")

        if kohals:                        # some copies available
            for loc in kohals:
                name, addr = resolve(loc)
                key = f"{name}|{addr}"
                local_copies[(author, title, key)] += 1
                local_meta[key] = (name, addr)
    # ---------------------------------------------------------------------

    total_kohal = sum(local_copies.values())
    if total_kohal:
        log("✓", f"{total_kohal} × KOHAL", "grn")
    else:
        log("✗", "0 × KOHAL", "red")
        FAILED.append(f"{author} – {title}"
                      + (f"  (ISBN {isbn})" if isbn else ""))

    log("⏳", f"{time.time() - t0:.2f}s", "pur")

    if DEBUG:
        for (a_, t_, key_), n_ in local_copies.items():
            log("DBG-copy", f"{key_:50}  +{n_}", "yel")

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
    if not addr:
        return None

    # already cached
    if not force and key in cache:
        if DEBUG:
            log("DBG-geo", f"cache {key:<45} → {cache[key]}", "dim")
        return tuple(cache[key])

    loc = geo(addr)            # Nominatim look-up (rate-limited)
    time.sleep(1)

    if loc:
        cache[key] = (loc.latitude, loc.longitude)
        gc_save(cache)
        if DEBUG:
            log("DBG-geo", f"fresh {key:<45} → {(loc.latitude, loc.longitude)}", "grn")
        return loc.latitude, loc.longitude

    log("!", f"geocode FAIL {addr}", "red", err=True)
    return None

def pcol(n: int) -> str:
    if n == 1:
        return "red"
    if n <= 3:
        return "orange"
    if n <= 7:
        return "beige"     # was 'yellow' → not accepted by folium.Icon
    return "green"

def build_map(lib_books, meta, coords, outfile):
    """
    lib_books   { key → [ "Author – Title", … ] }
    meta        { key → (nice_name, address) }
    coords      { key → (lat, lon) }
    outfile     output .html file
    """
    if not coords:
        log("!", "Nothing available (KOHAL) on ESTER", "yel", err=True)
        return

    # centre map on mean lat / lon
    lats = [la for la, _ in coords.values()]
    lons = [lo for _, lo in coords.values()]
    centre = (sum(lats) / len(lats), sum(lons) / len(lons))

    m = folium.Map(location=centre, zoom_start=11)

    # override Leaflet’s default 300 px CSS limit
    folium.Element(
        "<style>.leaflet-popup-content{max-width:1600px;}</style>"
    ).add_to(m)

    for key, books in lib_books.items():
        if key not in coords:
            continue            # should not happen, but be safe

        lat, lon = coords[key]
        name, _  = meta[key]

        html_popup = (
            f"<div style='{POPUP_CSS}'>"
            f"<b>{htm.escape(name)}</b><ul>"
            + "".join(f"<li>{htm.escape(b)}</li>" for b in books)
            + "</ul></div>"
        )

        folium.Marker(
            location=[lat, lon],
            popup=folium.Popup(
                html_popup,
                max_width=1600,     # ← widen the bubble
                min_width=300       #   and keep it from shrinking too much
            ),
            icon=folium.Icon(
                color=pcol(len(books)),
                icon="book",
                prefix="fa"
            ),
        ).add_to(m)

    m.save(outfile)
    log("✓", f"[Done] {outfile}", "grn")

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
