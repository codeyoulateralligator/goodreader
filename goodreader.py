#!/usr/bin/env python3
"""
goodreads_ester_mapper.py 🇪🇪📚
Build b-32 • 2025-07-02
"""

from __future__ import annotations
# ── stdlib ───────────────────────────────────────────────────────────
import argparse, csv, json, os, pathlib, re, sys, time, unicodedata, urllib.parse
from collections import Counter, defaultdict, deque   
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Tuple
# ── third-party ──────────────────────────────────────────────────────
import requests, folium, html
from bs4 import BeautifulSoup
from geopy.geocoders import Nominatim
from geopy.extra.rate_limiter import RateLimiter
import hashlib 
import urllib.parse as _uparse


# ─── debug helpers ───────────────────────────────────────────────────
DEBUG = bool(int(os.getenv("ESTER_DEBUG", "0")))
CLR = {k: f"\x1b[{v}m" for k, v in dict(dim=90, cyan=36, yel=33,
                                         grn=32, red=31, pur=35, reset=0).items()}
_WHITES = re.compile(r"\s{2,}")
def log(tag, msg, col="dim", err=False):
    stream = sys.stderr if err or DEBUG else sys.stdout
    print(f"{CLR[col]}{tag}{CLR['reset']} {msg}", file=stream, flush=True)
def dbg(tag, msg="", col="red"):
    if DEBUG:
        log(tag, msg, col)

FAILED: List[str] = []                 # titles with zero *KOHAL*
HTML_CACHE: dict[str, str] = {}
RECORD_URL: dict[tuple[str, str], str] = {}
RECORD_BRIEF: dict[str, str] = {}
RECORD_ISBN: dict[str, str] = {}       # record-url  →  isbn13
_BRIEF_CACHE: dict[str, str] = {} 
_ID_SEEN: set[str] = set()
_SURNAME_CLEAN = re.compile(r"[^a-z0-9]+")
_ERS_CACHE: dict[str, bool] = {}   # record-URL → verdict  (memo)

# ─── constants ───────────────────────────────────────────────────────
UA = "goodreads-ester/1.32"
HDRS = {"User-Agent": UA}
TIMEOUT, PAUSE = 30, 1      # sec
ESTER  = "https://www.ester.ee"
SEARCH = f"{ESTER}/search~S8*est"
GOODREADS_SHELF = "https://www.goodreads.com/review/list"

GEOCACHE = pathlib.Path(".geocache.json")
POPUP_CSS = ("font-size:1.5em;"
             "max-width:1000px;"
             "max-height:400px;"
             "overflow:auto;"
             "white-space:nowrap;")

_DASH = re.compile(r"[\u2010-\u2015\u2212]")
_SLUG = re.compile(r"[^A-Z0-9]")

# ─── static location tables (LIBRARY_META & BRANCH_META) ────────────
LIBRARY_META: Dict[str, Tuple[str, str]] = {
    "RaRa": ("Eesti Rahvusraamatukogu", "Tõnismägi 2, Tallinn, Estonia"),
    "TÜR": ("Tartu Ülikooli Raamatukogu", "W. Struve 1, Tartu, Estonia"),
    "TLÜAR": ("Tallinna Ülikooli Akadeemiline RK", "Rävala puiestee 10, Tallinn, Estonia"),
    "TalTech": ("TalTech Raamatukogu (peahoone)", "Akadeemia tee 1, Tallinn, Estonia"),
    "EKA": ("Eesti Kunstiakadeemia Raamatukogu", "Kotzebue 1, Tallinn, Estonia"),
    "EMU": ("Eesti Maaülikooli Raamatukogu", "Fr. R. Kreutzwaldi 1A, Tartu, Estonia"),
    "TlnRK": ("Tallinna Keskraamatukogu (süsteem)", "Estonia pst 8, Tallinn, Estonia"),
    "Tartu LR": ("Tartu Linnaraamatukogu", "Kompanii 3/5, Tartu, Estonia"),
    "KMAR": ("Kaitseväe Akadeemia Raamatukogu", "Riia 21, Tartu, Estonia"),
    "KV": ("Kaitseväe Peastaabi Raamatukogu", "Juhkentali 58, Tallinn, Estonia"),
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
def _slug(s): return _SLUG.sub("", unicodedata.normalize("NFKD", s)
                                            .encode("ascii","ignore").decode("ascii").upper())
BRANCH_META = {_slug(k): v for k, v in BRANCH_META.items()}

# ─── misc helpers ────────────────────────────────────────────────────
def squeeze(s):    return _WHITES.sub(" ", s)
def norm_dash(s):  return _DASH.sub("-", s)
def strip_parens(t): return re.sub(r"\s*\(.*?\)\s*$", "", t).strip()
def ester_enc(s):  return "".join(ch if ord(ch) < 128 else f"{{u{ord(ch):04X}}}" for ch in s)
def strip_ctrl(t): return "".join(ch for ch in t
                                  if unicodedata.category(ch)[0]!="C"
                                  and unicodedata.category(ch)!="Cf")

def _ascii_fold(s: str) -> str:
    """
    Strip accents/diacritics and return lowercase plain-ASCII.
    """
    return (
        unicodedata
        .normalize("NFKD", s)
        .encode("ascii", "ignore")
        .decode("ascii")
        .lower()
    )

def _surname(author: str) -> str:
    """
    Produce a sortable surname key.

    • Accepts both  “Lastname, Firstname”  (Goodreads CSV)
      and           “Firstname Lastname”   (occasional fallback).

    • Returned key is ASCII-folded, lowercase, and stripped of
      punctuation/diacritics, so “Saint-Exupéry” → “saintexupery”.
    """
    a = _ascii_fold(author)
    if "," in a:                                   # standard “Last, First”
        last = a.split(",", 1)[0]
    else:                                          # “First Last …”
        parts = _SURNAME_CLEAN.split(a)
        last = parts[-1] if parts else a
    return _SURNAME_CLEAN.sub("", last)            # purge leftovers

# ─── Goodreads CSV loader ────────────────────────────────────────────
def gd_csv(path: pathlib.Path, limit: int | None):
    out=[]
    with path.open(encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            if row.get("Exclusive Shelf","").lower()!="to-read": continue
            a = row["Author"].strip()
            t = row["Title"].strip()
            isbn = (row.get("ISBN13") or row.get("ISBN") or "").strip()
            if isbn.startswith('="') and isbn.endswith('"'): isbn = isbn[2:-1]
            out.append((a,t,isbn))
            if limit and len(out)>=limit: break
    return out

# ─── Goodreads web-shelf scraper (public profile) ────────────────────
def parse_web_shelf(uid: str, limit: int | None):
    """
    Scrape the public “table view” of a Goodreads user’s To-Read shelf.

    The ISBN column renders as:
        <span class="greyText">13</span>9789916127209
    so we MUST pick the *last* 13-digit substring.
    """
    out, page = [], 1
    while True:
        url = (f"{GOODREADS_SHELF}/{uid}"
               "?shelf=to-read&per_page=200"
               f"&page={page}&sort=date_added&view=table")
        soup = BeautifulSoup(_download(url), "html.parser")

        rows = soup.select("tr[id^='review_']")
        if not rows:
            break

        for r in rows:
            a = r.select_one("td.field.author   a")
            t = r.select_one("td.field.title    a")
            raw = r.select_one("td.field.isbn13")
            # take the LAST 13-digit run, ignore leading “13” label
            digits = re.findall(r"\b\d{13}\b", raw.get_text()) if raw else []
            isbn   = digits[-1] if digits else ""
            if a and t:
                out.append((a.get_text(strip=True),
                            t.get_text(strip=True),
                            isbn))
            if limit and len(out) >= limit:
                return out
        page += 1
    return out

# ─── put this near the other helpers ──────────────────────────────
def _canon_name(token: str) -> str:
    """
    Give a *lossy but stable* ASCII fingerprint for one surname token so that
    the countless spellings of the same Slavic/Baltic name collapse to the
    **same** string.

    Example collapses
    -----------------
        Aleksijevitš  →  alexivich
        Alexievits    →  alexivich
        Alexievich    →  alexivich
        Alexivich     →  alexivich   (already canonical)

    Pipeline
    --------
      0. lower-case
      1. digraph fixes that still carry diacritics   (tš→ch, dž→j, …)
      2. ASCII-fold remaining diacritics/umlauts
      3. cheap phonetic conflations                 (ks→x, hh→kh, j→y)
      4. collapse   double letters
      4½.   -vits / -ievits / -yevits   →   -vich
      5. glide simplifications           yi/iy/ie/ye  →  i
      6. drop trailing i/y glides
      7. strip everything that is *not* a–z
    """
    # ── 0. lower-case ────────────────────────────────────────────────
    s = token.lower()

    # ── 1. digraphs with diacritics (before ASCII-fold!) ─────────────
    s = (s.replace("tš", "ch")
           .replace("dž", "j"))

    # ── 2. ASCII-fold: map the few Estonian diacritics we meet ───────
    _TR = str.maketrans({
        "š": "sh", "ž": "zh",
        "õ": "o",  "ä": "a",
        "ö": "o",  "ü": "u",
    })
    s = s.translate(_TR)

    # ── 3. coarse phonetic conflations ───────────────────────────────
    s = (s.replace("ks", "x")      # Aleks → Alex
           .replace("hh", "kh")
           .replace("j", "y"))     # Иван → Ivan-y (й → y)

    # ── 4. collapse runs of doubled letters ──────────────────────────
    s = re.sub(r"(.)\1+", r"\1", s)

    # ── 4½. *-vits / -ievits / -yevits* → *-vich*  (most common case) ─
    s = re.sub(r"(?:[iey]?v)its$", "vich", s)

    # ── 5. glide simplifications  (yi/iy/ie/ye → i) ──────────────────
    #     This erases the e/ы difference responsible for
    #     Alexievich   vs  Alexivich    &c.
    s = (s.replace("yi", "i")
           .replace("iy", "i")
           .replace("ie", "i")
           .replace("ye", "i"))

    # ── 6. kill any leftover trailing i/y glide ──────────────────────
    s = re.sub(r"[iy]+$", "", s)

    # ── 7. allow only plain ASCII letters in the final key ───────────
    s = re.sub(r"[^a-z]", "", s)

    return s

_FRSCRUB = re.compile(r"""
     (?:&\d+(?:,\d+)*,?$)                 # tail like “…&1,1,” or “…&0,0,”
   | (?:[&?](?:save|saved|clear_saves)=[^&]*)   # ?save=…, &saved=…, …
""", re.I | re.X)

# ─── replace the whole _canon() with the version below ───────────────
def _canon(url: str) -> str:
    """
    Normalise *hit-list* URLs so that cosmetic junk
    (slice counters, “save” parameters) cannot generate
    an infinite stream of “new” pages.

    • If the link is a Sierra hit-list (contains “/frameset” anywhere)
      – keep the meaningful part up to &FF=…
      – strip trailing slice counters (&1,1, …) and the save/saved
        noise ESTER appends each time you click.
    • Otherwise drop the whole query string – ordinary pages don’t need it
      for uniqueness.
    """
    s = _uparse.urlsplit(url)
    path  = _uparse.unquote(s.path)
    query = _uparse.unquote(s.query)

    if "/frameset" in path or "/frameset" in query:
        tail = f"{path}?{query}" if query else path
        tail = _FRSCRUB.sub("", tail)                # ← NEW: scrub junk
        return _uparse.urlunsplit((s.scheme, s.netloc, tail, "", ""))

    # non-frameset: ignore ?params entirely
    return _uparse.urlunsplit((s.scheme, s.netloc, path, "", ""))

_MAX_VISITED = 60
_BAD_LEADS = (
    "/clientredirect", "/patroninfo~", "/validate/patroninfo",
    "/requestmulti~",  "/mylistsmulti", "/logout",

    # “Save record” noise produced by Sierra/ESTER
    "?save=",         #  ← NEW  (was only “&save=”)
    "&save=",
    "?saved=",        #  ← NEW
    "&saved=",
    "?clear_saves=",  #  ← NEW
    "&clear_saves=",
    "/frameset&save",     # old variant
    "?save_func=",
)

def collect_record_links(start_url: str) -> list[str]:
    """
    Breadth-first crawl starting at *start_url* and return the **first**
    physical ESTER record link (``.../record=bNNNNNNN~S8*est``) encountered.

    The walk stops as soon as one such link is found or after the safety
    limit of 60 distinct pages has been reached.

    Links whose URL matches anything in the `_BAD_LEADS` blacklist are
    skipped immediately – they are patron-session / redirect boiler-plate
    that can never contain holdings pages and often lead to infinite loops.
    """
    q: deque[str] = deque([start_url])
    seen: set[str] = set()

    while q:
        url = q.popleft()
        key = _canon(url)
        if key in seen:
            continue
        seen.add(key)

        dbg("collect open", url)
        soup = BeautifulSoup(_download(url), "html.parser")

        # ── 1. harvest record links already on this page ─────────────
        for a in soup.select('a[href*="/record=b"]'):
            rec = _uparse.urljoin(url, a["href"])
            if _is_eresource(rec):
                dbg("collect", f"    skip E-RES {rec[-28:]}")
                continue
            dbg("collect", f"    ✓ physical {rec[-28:]}")
            return [rec]                        # ← EARLY EXIT

        # ── 2. enqueue inner documents (framesets / iframes) ─────────
        leads = (
            [f["href"] for f in soup.select('a[href*="/frameset"]')] +
            [f["src"]  for f in soup.select('frame[src], iframe[src]')]
        )

        for l in leads:
            if not l:
                continue
            nxt = _uparse.urljoin(url, l)

            # skip anything on the do-not-touch list
            if any(bad in nxt or nxt.startswith(bad) for bad in _BAD_LEADS):
                dbg("collect", f"    skip bad-lead {nxt[:80]}")
                continue

            if _canon(nxt) in seen:
                continue
            if len(seen) >= _MAX_VISITED:
                dbg("collect", "    abort – visited>60")
                break

            q.append(nxt)
            dbg("collect", f"    add lead {nxt}")

    dbg("collect", "    ∅ 0 physical copies")
    return []

# ─── tokenisers / surname helper ─────────────────────────────────────
_norm_re=re.compile(r"[^a-z0-9]+")
def _ascii_fold(s): return unicodedata.normalize("NFKD",s).encode("ascii","ignore").decode("ascii").lower()
def _tokenise(s):   return {tok for tok in _norm_re.split(_ascii_fold(s)) if tok}
def _surname(a):    # supports “Lastname, Firstname”
    if "," in a: return _ascii_fold(a.split(",",1)[0]).split()[0]
    p=_ascii_fold(a).split(); return p[-1] if p else ""

# ─── HTTP download (cached) ──────────────────────────────────────────
SESSION = requests.Session()
def _download(url: str) -> str:
    if url in HTML_CACHE:
        return HTML_CACHE[url]
    try:
        r = SESSION.get(url, headers=HDRS, timeout=TIMEOUT, allow_redirects=True)
        r.raise_for_status()
    except requests.HTTPError as e:
        dbg("GET-ERR", f"{url[-60:]} → {e.response.status_code}")
        HTML_CACHE[url] = ""          # remember it’s useless
        return ""                     # let caller treat as “no data”
    HTML_CACHE[url] = r.text
    return r.text

# ─── ESTER utilities ────────────────────────────────────────────────
def _ester_fields(rec):
    soup=BeautifulSoup(_download(rec),"html.parser")
    ttl=soup.select_one("h1.title, h2.title") \
        or soup.select_one("td#bibTitle") \
        or soup.select_one("td.bibInfoLabel:-soup-contains('Pealkiri')+td.bibInfoData")
    aut=soup.select_one("td.bibInfoLabel:-soup-contains('Autor')+td.bibInfoData")
    return (strip_ctrl(ttl.get_text(" ",strip=True)) if ttl else "",
            strip_ctrl(aut.get_text(" ",strip=True)) if aut else "")

_ERS_TAGS = (
    "1 võrguressurss", "tekstifail", "audiofile", "videosalvestis",
    "võrguteavik", "1 online resource", "online resource",
    "electronic bk", "electronic resource",
    "e-raamat", "ebook", "e-audiobook", "e-raamat",
    "digitaalkogu", "internetiväljaanne", "pdf (online)", "pdf-fail",
    "www-link",
)

def _is_eresource(rec_url: str) -> bool:
    """
    Treat the record as a **virtual-only** item **iff**

      – the record page shows *no* holdings table **and**
      – at least one string from `_ERS_TAGS` occurs in the HTML.

    (Uses `_ERS_CACHE` for memoisation.)
    """
    if rec_url in _ERS_CACHE:             # memoised result → instant
        return _ERS_CACHE[rec_url]

    html = _download(rec_url)             # your existing cached GET
    soup = BeautifulSoup(html, 'html.parser')

    has_physical = bool(
        soup.select_one("tr.bibItemsEntry, tr[class*=bibItemsEntry]")
    )
    if has_physical:
        _ERS_CACHE[rec_url] = False
        dbg("_is_eresource", f"{rec_url} → False (physical holdings present)")
        return False

    page_lc = html.lower()
    eres    = any(tag.lower() in page_lc for tag in _ERS_TAGS)
    _ERS_CACHE[rec_url] = eres
    dbg("_is_eresource", f"{rec_url} → {eres}")
    return eres

# ---------------------------------------------------------------------
# _looks_like_same_book – new body with Slavic-name canonicalisation
# ---------------------------------------------------------------------
def _looks_like_same_book(w_ttl: str, w_aut: str, rec_url: str) -> bool:
    """
    Decide whether the ESTER record behind *rec_url* is the same book as
    (*w_ttl* /*w_aut*).  Returns True for a match.
    """
    # 1. pull title / author from the record page ---------------------
    r_ttl, r_aut = _ester_fields(rec_url)
    if not r_ttl:                        # fetch / parse failed
        return False

    # 2. tokenise -----------------------------------------------------
    wanted_toks = _tokenise(strip_parens(w_ttl))
    record_toks = _tokenise(r_ttl) | _tokenise(r_aut)

    # ---- TITLE test -------------------------------------------------
    ttl_ok = wanted_toks <= record_toks            # need *all* wanted words

    # ---- AUTHOR test (new) ------------------------------------------
    # a) take the surname part(s) of the wanted author
    surname_raw   = _surname(w_aut)                # “Aleksijevitš” etc.
    surname_parts = _tokenise(surname_raw)         # {'aleksijevits'}

    # b) canonicalise both sides to tolerate Aleksijevitš ↔ Alexievich
    wanted_canon  = {_canon_name(p) for p in surname_parts}
    record_canon  = {_canon_name(t) for t in record_toks}

    auth_ok = not surname_parts or wanted_canon <= record_canon

    # ---- DEBUG dump (unchanged) -------------------------------------
    if DEBUG:
        print("┌─  title/author comparator ──────────────────────────────────────")
        print(f"│  record URL      : {rec_url}")
        print(f"│  wanted ttl      : {w_ttl!r}")
        print(f"│  record ttl      : {r_ttl!r}")
        print(f"│  wanted aut      : {w_aut!r}")
        print(f"│  record aut      : {r_aut!r}")
        print(f"│  wanted toks     : {sorted(wanted_toks)}")
        print(f"│  record toks     : {sorted(record_toks)}")
        print(f"│  surname parts   : {sorted(surname_parts)}")
        print(f"│  canon wanted    : {sorted(wanted_canon)}")
        print(f"│  canon record    : {sorted(record_canon)}")
        verdict = 'MATCH' if ttl_ok and auth_ok else 'SKIP'
        colour  = 'grn' if verdict == 'MATCH' else 'red'
        print(f"└── verdict: {CLR[colour]}{verdict}{CLR['reset']}\n")

    return ttl_ok and auth_ok


# ──────────────────────────────────────────────────────────────────────
# Helper: pretty-print one (loc, status) pair
def _dbg_pair(tag: str, pair: tuple[str, str]):
    loc, sta = pair
    dbg(tag, f"{loc[:38]:38} {sta}")

# ──────────────────────────────────────────────────────────────────────
# ❶  Scrape one HTML holdings page
def _scrape_holdings_html(url: str) -> list[tuple[str, str]]:
    dbg("holdings", f"HTML→ {url}")
    html   = _download(url)
    dbg("holdings", f"      {len(html):,} B fetched")

    soup   = BeautifulSoup(html, "html.parser")
    rows   = soup.select("#tab-copies tr[class*='bibItemsEntry'], "
                         ".additionalCopies tr[class*='bibItemsEntry']")
    out: list[tuple[str, str]] = []
    for r in rows:
        tds = r.find_all("td")
        if len(tds) >= 3:
            out.append((strip_ctrl(tds[0].get_text()).strip(),
                        strip_ctrl(tds[2].get_text()).strip().upper()))

    dbg("holdings", f"      {len(out)} rows matched selector")
    if DEBUG and not out:
        dbg("holdings", "      saving HTML preview")
        with open("debug_empty_holdings.html", "w", encoding="utf-8") as fh:
            fh.write(html[:1200])            # write only first 1 200 B

    N = 2                             # how many rows to dump verbosely
    if DEBUG and out:
        for loc, sta in out[:N]:
            _dbg_pair("holdings", (loc, sta))
        if len(out) > N:
            dbg("holdings", f"... (+{len(out) - N} more)")

    return out

# ──────────────────────────────────────────────────────────────────────
# ❷  Ask EPiK JSON endpoint
def _copies_via_api(bib: str) -> list[tuple[str, str]]:
    api = "https://epik.ester.ee/api/data/getItemsByCodeList"
    dbg("holdings", f"API→ {api}  payload=[{bib!r}]")
    try:
        r = requests.post(api, json=[bib], timeout=10)
        dbg("holdings", f"      HTTP {r.status_code}, {len(r.content):,} B")
        r.raise_for_status()
        data = r.json()[0]            # list with one element
    except Exception as e:
        dbg("holdings", f"API error: {e}")
        return []

    items = data.get("items", [])
    dbg("holdings", f"      {len(items)} item objects")

    out: list[tuple[str, str]] = []
    for it in items:
        loc = it.get("libraryNameEst") or it.get("libraryName") or ""
        sta = (it.get("statusEst") or it.get("status") or "").upper()
        out.append((strip_ctrl(loc), strip_ctrl(sta)))

    if DEBUG and out:
        _dbg_pair("holdings", out[0])
        if len(out) > 1:
            _dbg_pair("holdings", out[1])

    return out

# ──────────────────────────────────────────────────────────────────────
# ❸  Master helper
def holdings(rec: str) -> list[tuple[str, str]]:
    """
    ① fetch …/holdings~   → parse
    ② fetch …/holdingsa~  → parse
    ③ EPiK JSON API       → parse
    returns [(location, STATUS), …]
    """
    m = re.search(r"\b(b\d{7})", rec)
    if not m:
        dbg("holdings", "cannot find bib-id in record URL")
        return []
    bib = m.group(1)

    # -- step ① : classic ---------------------------------------------
    base = (f"{ESTER}/search~S8*est?/.{bib}/.{bib}/1,1,1,B/holdings~{bib}"
            "&FF=&1,0,/indexsort=-")
    rows = _scrape_holdings_html(base)
    if rows:
        return rows

    # -- step ② : “available copies” page ------------------------------
    alt  = base.replace("holdings~", "holdingsa~")
    rows = _scrape_holdings_html(alt)
    if rows:
        return rows

    # -- step ③ : EPiK JSON -------------------------------------------
    dbg("holdings", "HTML empty – switching to EPiK API")
    return _copies_via_api(bib)

def resolve(loc):
    if loc.startswith("TlnRK"):
        rest=loc.removeprefix("TlnRK").lstrip(" ,:-")
        key=_slug(rest.split()[0]) if rest else ""
        return BRANCH_META.get(key,("Tallinna Keskraamatukogu","Tallinn")) if key else LIBRARY_META["TLKR"]
    for sig,(n,a) in LIBRARY_META.items():
        if loc.startswith(sig): return n,a
    return loc,""

# ─── colour helper (this was the missing bit) ────────────────────────
def pcol(n:int)->str:
    if n==1: return "red"
    if n<=3: return "orange"
    if n<=7: return "beige"
    return "green"

def _safe_id(raw: str) -> str:
    """
    Convert *raw* into a stable, HTML- and CSS-safe id attribute.
    - keep ASCII letters, numbers, '-' and '_'
    - collapse other runs of chars into a single '-'
    - guarantee uniqueness by appending a counter if needed
    """
    # 1. slugify
    slug = re.sub(r'[^0-9A-Za-z_-]+', '-', raw).strip('-_')
    if not slug:                                           # pathological case
        slug = 'id-' + hashlib.md5(raw.encode()).hexdigest()[:8]

    # 2. ensure uniqueness
    if slug in _ID_SEEN:
        base, n = slug, 2
        while f"{base}-{n}" in _ID_SEEN:
            n += 1
        slug = f"{base}-{n}"
    _ID_SEEN.add(slug)
    return slug
    
_BAD_IMG_PAT = re.compile(r'(?i)(/screens/|spinner|transparent\.gif|\.svg$)')
_GOOGLE      = "https://books.google.com/books/content?vid=ISBN{0}&printsec=frontcover&img=1&zoom=1"
_OPENLIB     = "https://covers.openlibrary.org/b/isbn/{0}-M.jpg"
IMG_ATTRS    = ("data-src", "data-original", "data-large", "data-iiif-high", "src")

# ── config  ──────────────────────────────────────────────────────────
_BAD_IMG_PAT = re.compile(
    r'''(?ix)
        /screens/            |   # Sierra placeholders
        spinner              |   # loading gifs
        transparent\.gif     |
        \.svg$               |   # any SVG → not a cover
        fonts\.gstatic\.com  # Google’s product logos (“g” icon)
    '''
)

def _looks_like_jacket(src: str) -> bool:
    return (
        src
        and (src.startswith(('http://', 'https://', '/iiif/'))
             or src.startswith('data:image/'))
        and not _BAD_IMG_PAT.search(src)
    )

def _abs(src: str) -> str:
    return src if src.startswith(("http", "data:")) else f"{ESTER}{src}"

def _scrape_isbns(soup: BeautifulSoup) -> list[str]:
    isbns = []
    for a in soup.select('a[href*="isbn"]'):
        m = re.search(r'\b\d{9}[\dXx]|\d{13}\b', a.get_text())
        if m:
            isbns.append(m.group(0))
    return isbns

_MIN_BYTES = 1337

def _first_good_url(urls: list[str]) -> str:
    for u in urls:
        try:
            r = requests.get(u, stream=True, timeout=5,
                             allow_redirects=True)
            ct   = r.headers.get("Content-Type", "")
            size = int(r.headers.get("Content-Length", 0) or 0)

            dbg(f"GET {u} → {r.status_code}  {ct}  {size:,} B")

            # ── NEW: skip Google-Books placeholder thumbs ───────────
            if ("books.google.com/books/content" in u
                    and size < 5_000):          # ← stricter limit
                continue                         # keep looking

            if r.ok and ct.startswith("image") and size >= _MIN_BYTES:
                return r.url                    # accept this one
        except Exception as e:
            dbg(f"Exception for URL {u}: {e}")
    return ""

# ─────────────────────────────────────────────────────────────────────
# NEW helper – write one compact gallery page with every cover found
# --------------------------------------------------------------------
# ────────────────────────────────────────────────────────────────────
def _write_covers_page(outfile: str = "all_covers.html") -> None:
    """
    Build a self-contained HTML gallery that shows every unique
    “Author – Title” together with the cover picked earlier.
    """
    # 1. gather unique snippets --------------------------------------
    gallery: list[tuple[str, str, str]] = []     # (surname key, title key, brief HTML)
    seen: set[str] = set()

    for (author, title), rec_url in RECORD_URL.items():
        brief = _record_brief(rec_url,
                              f"{author} – {title}",
                              RECORD_ISBN.get(rec_url, ""))
        if brief in seen:
            continue
        seen.add(brief)
        gallery.append((_surname(author), title.lower(), brief))

    if not gallery:        # nothing to show
        return

    gallery.sort()         # by surname, then title

    # 2. emit HTML ---------------------------------------------------
    with open(outfile, "w", encoding="utf-8") as fh:
        fh.write(
            "<!doctype html>\n<meta charset='utf-8'>\n"
            "<title>Goodreads → ESTER – kõik kaaned</title>\n"
            "<style>\n"
            " body{font-family:sans-serif;margin:1.4rem;}\n"
            " h1{margin:.2rem 0 1.2rem;font-size:1.8rem;}\n"
            " .grid{display:grid;gap:1.2rem;"
            "       grid-template-columns:repeat(auto-fit,minmax(180px,1fr));}\n"
            " figure{margin:0;text-align:center;border:1px solid #ccc;"
            "        padding:.6rem;border-radius:.4rem;background:#fafafa;"
            "        box-shadow:0 2px 4px rgba(0,0,0,.1);}\n"
            " figure img{max-width:100%;height:180px;object-fit:contain;"
            "            margin-bottom:.4rem;}\n"
            " figcaption{font-size:.88rem;line-height:1.25rem;}\n"
            " a{text-decoration:none;color:#036;}\n"
            " a:hover{text-decoration:underline;}\n"
            "</style>\n"
            "<h1>Kogu kaanekogu</h1>\n"
            "<section class='grid'>\n"
        )
        for _sk, _tk, brief in gallery:
            fh.write(f"  <figure>{brief}</figure>\n")
        fh.write("</section>")

    log("✓", f"[Done] {outfile}", "grn")


# ---------------------------------------------------------------------------
# smarter cover hunt with verbose logging
# ---------------------------------------------------------------------------
def _find_cover(
    soup: BeautifulSoup,
    *,
    author: str = "",
    title: str  = "",
    isbn_hint: str = ""
) -> str:
    """
    Return a usable jacket URL or "".
    Prints *all* URLs examined in order, together with the decision made.
    """
    tried: list[tuple[str, str]] = []          # (url, verdict)

    def _try(label: str, urls: list[str]) -> str:
        "Return first good URL or '' and log each attempt."
        for u in urls:
            verdict = "skip"
            try:
                r = requests.get(u, stream=True, timeout=5, allow_redirects=True)
                ct   = r.headers.get("Content-Type", "")
                size = int(r.headers.get("Content-Length", "0") or 0)
                if r.ok and ct.startswith("image") and size >= _MIN_BYTES:
                    verdict = f"OK ({size/1024:.1f} kB)"
                    tried.append((u, f"{label}: {verdict}"))
                    return r.url
                verdict = f"{ct or 'no-CT'} {size} B"
            except Exception as e:
                verdict = f"ERR {e.__class__.__name__}"
            finally:
                tried.append((u, f"{label}: {verdict}"))
        return ""

    # ── 0. inline <img> and og:image --------------------------------
    urls0 = []
    for tag in soup.select("img, noscript img"):
        for attr in IMG_ATTRS:
            src = (tag.get(attr) or "").strip()
            if _looks_like_jacket(src):
                urls0.append(_abs(src))
    og = soup.find("meta", property="og:image") or soup.find("meta", attrs={"name": "og:image"})
    if og and _looks_like_jacket(og.get("content", "")):
        urls0.append(_abs(og["content"]))
    if (hit := _try("inline/og", urls0)):
        dbg("cover-pick", hit)
        return hit

    # ── 1. EPiK avalanche & IIIF ------------------------------------
    code = (
        re.search(r'record=([b\d]+)', str(soup))
        or re.search(r'catalog/([b\d]+)', str(soup))
        or re.search(r'"code"\s*:\s*"([b\d]+)"', str(soup))
    )
    if code:
        code = code.group(1)
        urls1 = [
            f"https://www.ester.ee/iiif/2/{code}/full/500,/0/default.jpg"
        ]
        # ask avalanche once
        try:
            js = requests.post(
                "https://epik.ester.ee/api/data/getImagesByCodeList",
                json=[code], timeout=8
            ).json()[0]
            if js.get("imageData"):
                b64 = js["imageData"]
                # if the embedded cover is crazy large (> 300 kB) prefer urlLarge
                if len(b64) > 300_000 and (js.get("urlLarge") or js.get("urlSmall")):
                    urls1 += [js.get("urlLarge") or js.get("urlSmall")]
                else:
                    full_uri = "data:image/jpeg;base64," + b64
                    tried.append((
                        "data:image/jpeg;base64," + b64[:60] + "…",
                        f"avalanche: inline base-64 ({len(b64)/1024:.0f} kB)"))
                    dbg("cover-pick", "inline base-64")
                    return full_uri
            urls1 += [js.get("urlLarge") or js.get("urlSmall") or ""]
        except Exception:
            pass
        if (hit := _try("avalanche/iiif", urls1)):
            dbg("cover-pick", hit)
            return hit

    # ── 2. Google-Books thumb by ISBN --------------------------------
    isbn_list = _scrape_isbns(soup) or ([isbn_hint] if isbn_hint else [])
    urls2 = [_GOOGLE.format(i) for i in isbn_list]
    if (hit := _try("gbooks", urls2)):
        dbg("cover-pick", hit)
        return hit

    # ── 3. OpenLibrary by ISBN ---------------------------------------
    urls3 = [_OPENLIB.format(i) for i in isbn_list]
    if (hit := _try("openlib", urls3)):
        dbg("cover-pick", hit)
        return hit

    # ── 4. Google Images “author title book cover” -------------------
    q = f"{author} {title} book cover".strip()
    gimg = _first_google_image(q)
    if gimg:
        if (hit := _try("gimages", [gimg])):
            dbg("cover-pick", hit)
            return hit

    # ── nothing worked ----------------------------------------------
    dbg("cover-pick", "EMPTY")
    # Dump the decision log in DEBUG mode
    if DEBUG:
        for url, verdict in tried:
            print(f"   • {verdict:25} → {url}")
    return ""

def _record_brief(rec, fallback_title: str = "", isbn: str = "") -> str:
    """
    Return a one-liner HTML fragment for use inside the Leaflet pop-up.
    • *rec* may be  – record-URL  |  raw HTML  |  BeautifulSoup node
    • *fallback_title* is the plain “Author – Title” string you already know
    • *isbn* lets _find_cover() and the OpenLibrary fallback try ISBN routes
    """
    # ── 1. get / parse the record page ───────────────────────────────
    soup: BeautifulSoup | None = None
    url: str | None            = None

    if hasattr(rec, "select_one"):               # soup or Tag
        soup = (rec if isinstance(rec, BeautifulSoup)
                else BeautifulSoup(str(rec), "html.parser"))

    elif isinstance(rec, str):
        if rec.startswith("http"):               # URL
            url = rec
            if url in _BRIEF_CACHE:              # memoised → done
                return _BRIEF_CACHE[url]

            soup = BeautifulSoup(_download(url), "html.parser")
        else:                                    # raw HTML
            soup = BeautifulSoup(rec, "html.parser")

    # ── 2. extract title / author (fallbacks keep page usable) ───────
    title = author = ""
    if soup:
        ttl_el = (soup.select_one(".bibInfoData strong")
                  or soup.select_one("h1.title, h2.title, td#bibTitle"))
        aut_el = (soup.select_one(".bibInfoData a[href*='/author']")
                  or soup.select_one(
                        "td.bibInfoLabel:-soup-contains('Autor')+td.bibInfoData"))
        title  = ttl_el.get_text(strip=True) if ttl_el else ""
        author = aut_el.get_text(strip=True) if aut_el else ""

    if not title:                                # last-ditch fallback
        title = (fallback_title.split(" – ", 1)[1]
                 if " – " in fallback_title else fallback_title or "—")

    # ── 3. cover hunt ────────────────────────────────────────────────
    cover = ""
    if soup:
        cover = _find_cover(
            soup=soup,
            author=author,
            title=title,
            isbn_hint=isbn
        )

    # **only** if nothing worked above, try OpenLibrary by ISBN
    if not cover and isbn:
        cover = _openlib_link(isbn, "M")     # ?default=false is in helper

    # <img> with auto-vanish on 4xx/403 etc.
    cover_html = (
        f'<img src="{cover}" loading="lazy" '
        f'style="height:120px;float:right;margin-left:.6em;" '
        f'onerror="this.remove();">'
        if cover else ""
    )

    # ── 4. compose final snippet & memoise ───────────────────────────
    link_start = (f'<a href="{html.escape(url)}" target="_blank" '
                  f'rel="noopener noreferrer">') if url else ""
    link_end   = "</a>" if url else ""

    text = (f"{html.escape(author)} – <em>{html.escape(title)}</em>"
            if author else f"<em>{html.escape(title)}</em>")

    brief = f"{cover_html}{link_start}{text}{link_end}"

    if url:
        _BRIEF_CACHE[url] = brief

    return brief

_JS_SNIPPET = r"""
<script>
/* Helper: rebuild the heading line on demand ------------------------ */
function headingHTML(hasSel){
  return (hasSel
            ? '<button id="closeSel" onclick="clearSelection()" '
              + 'style="float:right;font-weight:bold;background:#eee;'
              + 'border:1px solid #999;border-radius:3px;width:1.6em;'
              + 'height:1.6em;line-height:1.2em;cursor:pointer;">&times;</button>'
            : '')
       + '<h3 style="margin:0;">Valitud raamatud</h3>';
}

/* Simple HTML-entity unescape for tooltips -------------------------- */
function decodeHTML(str){
  const t = document.createElement('textarea');
  t.innerHTML = str;
  return t.value;
}

const chosen = new Map();

/* Re-render the panel ------------------------------------------------ */
function refreshPanel(){
  const box     = document.getElementById("selectionBox");
  const hasSel  = chosen.size > 0;
  const items   = Array.from(chosen.values())
                       .map(txt => "<p>"+txt+"</p>")
                       .join("<hr style='margin:.4em 0;width:100%;'>");
  box.innerHTML = headingHTML(hasSel) + items;
}

/* Clear everything --------------------------------------------------- */
function clearSelection(){
  for (const id of chosen.keys()){
    const li = document.getElementById(id);
    if (li) li.style.fontWeight = "normal";
  }
  chosen.clear();
  refreshPanel();
}

/* Toggle one book in/out of the list --------------------------------- */
function toggleBook(id){
  const li = document.getElementById(id);
  if (chosen.has(id)){
    chosen.delete(id);
    li.style.fontWeight = "normal";
  } else {
    chosen.set(id, decodeHTML(li.dataset.brief));
    li.style.fontWeight = "bold";
  }
  refreshPanel();
}
</script>

<style>
#selectionBox{
  position:fixed; top:1rem; right:1rem; z-index:9999;
  max-width:340px; max-height:90vh; overflow:auto;
  background:#fff; border:2px solid #444; padding:0.5rem 1rem;
  box-shadow:0 0 8px rgba(0,0,0,.3); font-size:0.9em;
}
</style>

<!-- initial empty panel -->
<div id="selectionBox">
  <!-- headingHTML(false) -->
  <h3 style="margin:0;">Valitud raamatud</h3>
</div>
"""

# ── helper: take first Google Images hit ─────────────────────────────
def _first_google_image(query: str) -> str:
    """
    Return the first *usable* image URL from Google Images quick-results.
    (Tiny SVG/GIF placeholders are ignored.)
    """
    try:
        # lightweight ‘tbm=isch’ request
        page = requests.get(
            "https://www.google.com/search",
            params={"q": query, "tbm": "isch", "ijn": "0"},
            headers={"User-Agent": UA},
            timeout=6
        ).text
        # first <img … src=…>
        for m in re.finditer(r'<img[^>]+src="([^"]+)"', page):
            url = html.unescape(m.group(1))
            # skip logos, SVGs, transparent GIFs, etc.
            if _BAD_IMG_PAT.search(url) or url.lower().endswith(".svg"):
                continue
            return url
    except Exception:
        pass
    return ""

# ─── search helpers ──────────────────────────────────────────────────
def _probe(label: str, url: str) -> list[str]:
    """
    Run one ESTER probe, log its hit-count *and* the probe-URL, then
    return the list of record links that were found.
    """
    # crawl the URL and collect record links
    links = collect_record_links(url)
    hits  = len(links)

    # colour for the progress line (green when there are hits)
    colour = "grn" if hits else "red"

    # diagnostic summary
    log("🛰 probe", f"{label:<14} {hits} hit(s)", colour)
    log("↳", url, "dim")   # always show the exact probe URL

    return links


def by_isbn(isbn): 
    return _probe("keyword-isbn",f"{SEARCH}/X?searchtype=X&searcharg={isbn}"
                                               "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
def by_title_index(t, *, _label="title-idx"):
    q = ester_enc(norm_dash(t))
    return _probe(_label, f"{SEARCH}/X?searchtype=t&searcharg="
                          f"{urllib.parse.quote_plus(q,safe='{}')}"
                          "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
def by_keyword(a, t, *, _label="keyword-ttl"):
    raw = squeeze(f"{a} {t}")
    q   = ester_enc(norm_dash(raw))
    return _probe(_label, f"{SEARCH}/X?searchtype=X&searcharg="
                          f"{urllib.parse.quote_plus(q,safe='{}')}"
                          "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")

def search(author: str, title: str, isbn: str) -> list[str]:
    """
    Return **at most one** ESTER record URL – the first one that fits.

    Strategy
    --------
      1. ISBN (unique)             → accept immediately if a physical record is found
      2. title-index search        → require title/author token match
      3. keyword  “author title”   → ditto
      4. keyword  “title”          → ditto
    """
    # -- normalise ----------------------------------------------------
    title = strip_parens(title)

    # -- ① ISBN probe -------------------------------------------------
    if isbn:
        links = by_isbn(isbn)
        if links:
            # The catalogue confirmed the ISBN and the record is physical
            return links[:1]           # short-circuit – no extra checks

    # -- ②–④ fallback probes -----------------------------------------
    probes = (
        (by_title_index,               (title,),            "title-idx"),
        (by_keyword,      (author,     title),              "kw-author+title"),
        (by_keyword,      ("",         title),              "kw-title-only"),
    )

    for fn, args, lbl in probes:
        # skip probes whose arguments are completely empty
        if not any(args):
            continue

        # forward the explicit label so _probe() prints it
        links = fn(*args, _label=lbl)

        for rec in links:                     # validate on the fly
            if _looks_like_same_book(title, author, rec):
                return [rec]                  # first convincing hit

    return []

# ─── worker ──────────────────────────────────────────────────────────
def _openlib_link(isbn13: str, size: str = "M") -> str:
    # size = S | M | L   – whatever you prefer
    return (
        f"https://covers.openlibrary.org/b/isbn/{isbn13}-{size}.jpg"
        "?default=false"          # << *** key change  ***
    )   

# ─── worker ──────────────────────────────────────────────────────────
def process_title(idx: int, total: int,
                  author: str, title: str, isbn: str) -> tuple[Counter, dict]:
    """
    • log progress
    • call `search()`
    • collect *KOHAL* holdings for the (single) matching record
    """
    t0 = time.time()
    log(f"[{idx:3}/{total}]", f"{author} – {title}", "cyan")
    log("🔖 ISBN:", isbn or "— none —", "pur")

    copies: Counter                   = Counter()
    meta:   dict[str, tuple[str, str]] = {}

    recs = search(author, title, isbn)
    if not recs:                                      # zero matches
        log("✗", "no matching record on ESTER", "red")
        FAILED.append(f"{author} – {title}" + (f" (ISBN {isbn})"
                                               if isbn else ""))
        log("⏳", f"{time.time() - t0:.2f}s", "pur")
        return copies, meta

    rec = recs[0]                                     # exactly one
    RECORD_URL[(author, title)] = rec
    RECORD_ISBN[rec]            = isbn or ""
    _record_brief(rec, f"{author} – {title}", isbn or "")

    # ── holdings ------------------------------------------------------------
    for loc, status in holdings(rec):
        name, addr = resolve(loc)
        key        = f"{name}|{addr}"

        if "KOHAL" in status:
            copies[(author, title, key)] += 1

        meta[key] = (name, addr)

    tot = sum(copies.values())
    log("✓" if tot else "✗",
        f"{tot} × KOHAL" if tot else "0 × KOHAL",
        "grn" if tot else "red")

    if not tot:
        FAILED.append(f"{author} – {title}"
                      + (f" (ISBN {isbn})" if isbn else ""))

    log("⏳", f"{time.time() - t0:.2f}s", "pur")
    return copies, meta

# ─── map builder ─────────────────────────────────────────────────────
def build_map(lib_books, meta, coords, outfile):
    """
    lib_books { key → [(display, url)  OR  display_string, …] }
    meta      { key → (pretty_name, address) }
    coords    { key → (lat, lon) }
    """
    if not coords:
        log("!", "Nothing available (KOHAL) on ESTER", "yel", err=True)
        return

    # ── centre the map roughly on the mean location ────────────────
    lats = [la for la, _ in coords.values()]
    lons = [lo for _, lo in coords.values()]
    centre = (sum(lats) / len(lats), sum(lons) / len(lons))

    m = folium.Map(location=centre, zoom_start=11)
    folium.Element(
        "<style>.leaflet-popup-content{max-width:1600px;}</style>"
    ).add_to(m)

    # include the JS/CSS for the “selection” side-panel
    m.get_root().html.add_child(folium.Element(_JS_SNIPPET))

    # ── iterate every library that has copies ───────────────────────
    for key, entries in lib_books.items():
        if key not in coords:
            continue
        lat, lon = coords[key]
        lib_name, _addr = meta[key]

        # ── NEW: sort list items by author surname (case-/accent-less) ──
        def _sort_key(entry):
            disp = entry[0] if isinstance(entry, (tuple, list)) else entry
            author_part = disp.split("–", 1)[0].strip()      # “Lastname, Firstname”
            return _surname(author_part)

        entries_sorted = sorted(entries, key=_sort_key)

        # ── build the <li> elements (unchanged except we use entries_sorted) ──
        lis = []
        for entry in entries_sorted:
            disp, url = (
                (entry[0], entry[1]) if isinstance(entry, (tuple, list))
                else (entry, "")
            )
            elem_id = _safe_id(lib_name + disp)
            brief_html = (
                _record_brief(url, disp, RECORD_ISBN.get(url, ""))
                if url else html.escape(disp)
            )
            brief_attr = (
                brief_html.replace("&", "&amp;")
                          .replace('"', "&quot;")
                          .replace("'", "&#39;")
            )
            lis.append(
                f'<li id="{elem_id}" data-brief="{brief_attr}" '
                f'style="cursor:pointer;color:#06c;" '
                f'onclick="event.stopPropagation();toggleBook(\'{elem_id}\')">'
                f'{html.escape(disp)}</li>'
            )

        html_popup = (
            f"<div style='{POPUP_CSS}'>"
            f"<b>{html.escape(lib_name)}</b> "
            f"<span style='color:#666;font-size:90%;'>"
            f"({len(entries_sorted)} pealkirja)</span>"
            f"<ul>{''.join(lis)}</ul></div>"
        )

        folium.Marker(
            location=[lat, lon],
            popup=folium.Popup(html_popup, max_width=1600, min_width=300),
            icon=folium.Icon(color=pcol(len(entries_sorted)),
                             icon="book", prefix="fa"),
        ).add_to(m)

    # ── write file ──────────────────────────────────────────────────
    m.save(outfile)
    log("✓", f"[Done] {outfile}", "grn")

# ─── main entry-point ────────────────────────────────────────────────
def main():
    global DEBUG
    ap=argparse.ArgumentParser()
    gx=ap.add_mutually_exclusive_group(required=True)
    gx.add_argument("--goodreads-csv",type=pathlib.Path)
    gx.add_argument("--goodreads-user")
    ap.add_argument("--max-titles",type=int)
    ap.add_argument("--geocode",action="store_true")
    ap.add_argument("--debug",action="store_true")
    ap.add_argument("--threads",type=int,default=1)
    ap.add_argument("--output",type=pathlib.Path,default="want_to_read_map.html")
    a=ap.parse_args(); DEBUG|=a.debug

    t0 = time.time()

    titles=gd_csv(a.goodreads_csv,a.max_titles) if a.goodreads_csv \
          else parse_web_shelf(a.goodreads_user,a.max_titles)
    log("ℹ",f"{len(titles)} titles","cyan")

    copies=Counter(); meta={}
    if a.threads==1:
        for i,(au,ti,isbn) in enumerate(titles,1):
            c,m=process_title(i,len(titles),au,ti,isbn); copies.update(c); meta.update(m)
    else:
        with ThreadPoolExecutor(max_workers=max(1,a.threads)) as p:
            fut=[p.submit(process_title,i,len(titles),au,ti,isbn)
                 for i,(au,ti,isbn) in enumerate(titles,1)]
            for f in as_completed(fut):
                c,m=f.result(); copies.update(c); meta.update(m)

    if not copies:
        log("!", "Nothing available (KOHAL) on ESTER","red",err=True); return

    lib_books = defaultdict(list)          # key → [(display,url), …]
    for (au, ti, key), n in copies.items():
        display = f"{au} – {ti}" + (f" ({n}×)" if n > 1 else "")
        url     = RECORD_URL.get((au, ti), "")     # may be empty
        lib_books[key].append((display, url))

    geocoder=RateLimiter(Nominatim(user_agent=UA).geocode,min_delay_seconds=1)
    cache=json.loads(GEOCACHE.read_text()) if GEOCACHE.exists() else {}
    coords={}
    for k,(name,addr) in meta.items():
        if not addr: continue
        if not a.geocode and k in cache: coords[k]=cache[k]; continue
        loc=geocoder(addr); time.sleep(1)
        if loc: coords[k]=(loc.latitude,loc.longitude); cache[k]=coords[k]
    if coords: GEOCACHE.write_text(json.dumps(cache,indent=2,ensure_ascii=False))
    build_map(lib_books,meta,coords,a.output)

    if FAILED:
        log("\n=== TITLES WITH NO *KOHAL* COPIES ===","","red")
        for line in FAILED: log("✗",line,"red")
        log(f"Total missing: {len(FAILED)}","","red")

    log("ℹ", "Writing cover gallery page", "cyan")
    _write_covers_page("all_covers.html")

    total_time = time.time() - t0
    log("⏱", f"Total time spent: {total_time:.2f}s", "yel")

if __name__=="__main__":
    main()
