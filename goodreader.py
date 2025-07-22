#!/usr/bin/env python3
"""
goodreader.py 🇪🇪📚
Build b-33 • 29-06-2025
github.com/codeyoulateralligator
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
from urllib3.util.retry import Retry
from requests.adapters   import HTTPAdapter
from metaphone import doublemetaphone

# ─── debug helpers ───────────────────────────────────────────────────
DEBUG = bool(int(os.getenv("ESTER_DEBUG", "0")))
CLR = {k: f"\x1b[{v}m" for k, v in dict(dim=90, cyan=36, yel=33,
                                         grn=32, red=31, pur=35, white=39, reset=0).items()}
_WHITES = re.compile(r"\s{2,}")
def log(tag, msg="", col="white", err=False):
    stream = sys.stderr if err or DEBUG else sys.stdout
    print(f"{CLR[col]}{tag}{CLR['reset']} {msg}", file=stream, flush=True)

def dbg(tag, msg="", col="cyan"):
    if DEBUG:
        log(tag, msg, col)

def dbg_pair(tag: str, pair: tuple[str, str]):
    loc, sta = pair
    dbg(tag, f"{loc[:38]:38} {sta}")

NOT_FOUND: List[str] = []                # search returned zero records
NO_KOHAL:  List[str] = []                # record exists, but 0 × KOHAL
HTML_CACHE: dict[str, str] = {}
RECORD_URL: dict[tuple[str, str], str] = {}
RECORD_BRIEF: dict[str, str] = {}
RECORD_ISBN: dict[str, str] = {}         # record-url  →  isbn13
BRIEF_CACHE: dict[str, str] = {} 
ID_SEEN: set[str] = set()
SURNAME_CLEAN = re.compile(r"[^a-z0-9]+")
ERS_CACHE: dict[str, bool] = {}          # record-URL → verdict  (memo)
COVER_SRC   : Counter[str] = Counter()   # per source “inline/og”, “gbooks”, …
BOOKS_WITH_COVER = 0                     # total books that ended up with a cover
GR_META: dict[str, tuple[str, str]] = {}
GOODREADS_URL: dict[tuple[str, str], str] = {}   # (author, title) → permalink
CALLNUMS: defaultdict[tuple[str, str, str], list[str]] = defaultdict(list)

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
        parts = SURNAME_CLEAN.split(a)
        last = parts[-1] if parts else a
    return SURNAME_CLEAN.sub("", last)            # purge leftovers

# ─── Goodreads CSV loader ────────────────────────────────────────────
def gd_csv(path: pathlib.Path, limit: int | None):
    log(f"Loading Goodreads CSV from {path}")
    out = []
    with path.open(encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            if row.get("Exclusive Shelf", "").lower() != "to-read":
                continue

            author = row["Author"].strip()
            title  = row["Title"].strip()

            # ------------ NEW: store permalink if “Book Id” column exists ---
            if bid := row.get("Book Id", "").strip():
                GOODREADS_URL[(author, title)] = (
                    f"https://www.goodreads.com/book/show/{bid}"
                )

            # ISBN extraction as before
            isbn = (row.get("ISBN13") or row.get("ISBN") or "").strip()
            if isbn.startswith('="') and isbn.endswith('"'):
                isbn = isbn[2:-1]

            out.append((author, title, isbn))
            if limit and len(out) >= limit:
                break
    return out

# ─── Goodreads web-shelf scraper (public profile) ────────────────────
def parse_web_shelf(uid: str, limit: int | None):
    log(f"Scraping Goodreads shelf for {uid}")
    out, page = [], 1
    while True:
        url = (f"{GOODREADS_SHELF}/{uid}"
               "?shelf=to-read&per_page=200"
               f"&page={page}&sort=date_added&view=table")
        log("→", url)
        soup = BeautifulSoup(_download(url), "html.parser")
        log("→", f"HTML {len(soup.encode()):,} B")

        rows = soup.select("tr[id^='review_']")
        if not rows:
            break

        for r in rows:
            a_tag = r.select_one("td.field.title a")
            au_tag = r.select_one("td.field.author a")
            raw_isbn = r.select_one("td.field.isbn13")

            if not (a_tag and au_tag):
                continue

            author = au_tag.get_text(strip=True)
            title  = a_tag.get_text(strip=True)
            # ---------- NEW: store the direct link -------------------------
            GOODREADS_URL[(author, title)] = (
                "https://www.goodreads.com" + a_tag["href"].split("?")[0]
            )

            digits = re.findall(r"\b\d{13}\b", raw_isbn.get_text())
            isbn   = digits[-1] if digits else ""
            out.append((author, title, isbn))

            if limit and len(out) >= limit:
                return out
        page += 1
    return out

def dual_link(author: str,
               title:  str,
               *,
               ester: str = "",
               isbn:  str = "") -> str:
    """
    Return tiny tag(s) in square brackets:

        [E] – exact ESTER record   (omitted if *ester* == "")
        [G] – exact Goodreads page (ISBN ▸ permalink ▸ search fallback)

    Always opens in a new tab; tags separated by a thin space (&nbsp;).
    """
    # -------- decide Goodreads URL ----------------------------------------
    if re.fullmatch(r"\d{13}", isbn):
        gr_url = f"https://www.goodreads.com/book/isbn/{isbn}"
    else:
        gr_url = GOODREADS_URL.get((author, title))
        if not gr_url:
            q = urllib.parse.quote_plus(f"{author} {title}")
            gr_url = f"https://www.goodreads.com/search?q={q}"

    est_tag = (f'<a href="{ester}" target="_blank" rel="noopener" '
               f'title="ESTER">[E]</a>&nbsp;' ) if ester else ""
    gr_tag  = (f'<a href="{gr_url}" target="_blank" rel="noopener" '
               f'title="Goodreads">[G]</a>')

    return est_tag + gr_tag

# 1. **single-char** fixes that can go into translate()
_DEFANG = str.maketrans({
    "ё": "o",
    "œ": "o",
})

# 2. **multi-char** substitutions – keep them here, apply with .replace()
_MULTI = {
    "oe": "o",           # Dost**oe**v–
    "yo": "o", "jo": "o", "io": "o",
    "ya": "a", "ja": "a",
}

# cheap clean-ups
_SK_FAMILY  = re.compile(r"(sky|ski|skij|skyi)$")   # –ski → –sk
_DBL_LETTER = re.compile(r"(.)\1+")                 # collapse doubles
_NONAZ      = re.compile(r"[^a-z]")                 # drop non-letters

def _canon_name(token: str) -> str:
    """
    Return **one short ASCII fingerprint** for any Slavic/Baltic surname:
        • normalise diacritics/umlauts
        • fold common multi-graph variants  (ё/oe/yo …)
        • collapse double letters, -ski → -sk, …
        • finally → Double Metaphone → first code  (eg. 'KRMST' for Karamazov)

    If Metaphone yields an empty string (rare), fall back to the
    stripped-ASCII version instead.
    """
    s = token.lower()

    # NEW ❶: neutralise -jev-/-jov- glides before anything else
    s = re.sub(r"[jy][eo]v", "ev", s)    # jev / jov → ev

    # 0. apply multi-char replacements first
    for pat, repl in _MULTI.items():
        s = s.replace(pat, repl)

    # 1. one-char translate
    s = s.translate(_DEFANG)

    # 2. ASCII-fold the rest of the diacritics
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()

    # 3. cheap conflations
    s = _SK_FAMILY.sub("sk", s)          # Dostojevski  →  Dostojevsk
    s = _DBL_LETTER.sub(r"\1", s)        # kk → k,   yy → y
    s = _NONAZ.sub("", s)                # only [a-z]

    # 4. Double Metaphone
    code = doublemetaphone(s)[0]
    return code or s                     # safety fallback

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

_MAX_VISITED = 13
_BAD_LEADS = (
    "/clientredirect", "/patroninfo~", "/validate/patroninfo",
    "/requestmulti~",  "/mylistsmulti", "/logout",

    # “Save record” noise produced by Sierra/ESTER
    "?save=",
    "&save=",
    "?saved=",
    "&saved=",
    "?clear_saves=",
    "&clear_saves=",
    "/frameset&save",
    "?save_func=",
)

# ────────────────────────────────────────────────────────────────────
# NEW  collect_record_links  – gather *all* physical records
# ────────────────────────────────────────────────────────────────────
def collect_record_links(start_url: str,
                         limit: int | None = None) -> list[str]:
    """
    Crawl from *start_url* (frameset or plain list) and return physical-copy
    book record URLs.

    Every candidate link is logged **exactly once** with a tidy, aligned
    verdict so the DEBUG stream is easy to scan:

        collect open         https://…/frameset&FF=tubik
        collect + physical   https://…/record=b1784914~S8*est
        collect - duplicate  https://…/record=b1784914~S8*est
        collect - e-resource https://…/record=b5362798~S8*est

    Legend
    ------
    + physical    ─ accepted, added to *out*
    - duplicate   ─ we already have that record
    - e-resource  ─ virtual-only, no physical copies
    - non-book    ─ CD / DVD / etc.

    The crawl stops when either *limit* accepted records are gathered
    or more than `_MAX_VISITED` distinct HTML pages were visited.
    """
    q: deque[str] = deque([start_url])
    seen_pages: set[str] = set()
    out: list[str]      = []

    # helper: one **uniformly padded** log-line -----------------------
    def _col(kind: str, txt: str, colour: str = "dim") -> None:
        dbg("collect", f"{kind:<12}  {txt}", colour)    # 12-char slot

    # helper: verdict wrapper so we don’t repeat colour tables --------
    def _verdict(rec: str, tag: str) -> None:
        _col(tag, rec, {
            "+ physical"  : "grn",
            "- duplicate" : "dim",
            "- e-resource": "dim",
            "- non-book"  : "dim",
        }.get(tag, "dim"))

    # ────────────────────────────────────────────────────────────────
    while q:
        url = q.popleft()
        key = _canon(url)
        if key in seen_pages:
            continue
        seen_pages.add(key)

        _col("open", url, "cyan")                    # page we’re fetching
        soup = BeautifulSoup(_download(url), "html.parser")

        # 1. harvest record links on this page -----------------------
        for a in soup.select('a[href*="/record=b"]'):
            rec = _uparse.urljoin(url, a["href"])

            if _is_eresource(rec):
                _verdict(rec, "- e-resource")
                continue
            if _is_nonbook(rec):
                _verdict(rec, "- non-book")
                continue
            if rec in out:
                _verdict(rec, "- duplicate")
                continue

            out.append(rec)
            _verdict(rec, "+ physical")

            if limit and len(out) >= limit:          # early stop
                return out

        # 2. follow inner frames / iframes ---------------------------
        leads = (
            [f["href"] for f in soup.select('a[href*="/frameset"]')] +
            [f["src"]  for f in soup.select('frame[src], iframe[src]')]
        )

        for l in leads:
            if not l:
                continue
            nxt = _uparse.urljoin(url, l)
            if any(bad in nxt or nxt.startswith(bad) for bad in _BAD_LEADS):
                continue
            if _canon(nxt) in seen_pages:
                continue
            if len(seen_pages) >= _MAX_VISITED:
                _col("abort", f"visited>{_MAX_VISITED}", "red")
                return out
            q.append(nxt)

    return out

# ─── tokenisers / surname helper ─────────────────────────────────────
_norm_re=re.compile(r"[^a-z0-9]+")
def _ascii_fold(s): return unicodedata.normalize("NFKD",s).encode("ascii","ignore").decode("ascii").lower()
def _tokenise(s):   return {tok for tok in _norm_re.split(_ascii_fold(s)) if tok}
def _surname(a):    # supports “Lastname, Firstname”
    if "," in a: return _ascii_fold(a.split(",",1)[0]).split()[0]
    p=_ascii_fold(a).split(); return p[-1] if p else ""

# ─── HTTP download (cached + retry) ─────────────────────────────────
SESSION = requests.Session()

# ① optional: mount a Retry-enabled adapter so we also recover from the
#    occasional 5xx when Goodreads hiccups

_retry = Retry(total=3,
               backoff_factor=2.0,           # 0 s, 2 s, 4 s …
               status_forcelist=[502, 503, 504],
               allowed_methods=["GET", "HEAD"])
SESSION.mount("https://", HTTPAdapter(max_retries=_retry))
SESSION.mount("http://",  HTTPAdapter(max_retries=_retry))

# ② our own thin retry wrapper for *timeouts* -----------------------
def _download(url: str, *, tries: int = 3,
              connect_t: int = 8, read_t: int = 60) -> str:
    """
    GET *url* with small in-memory cache.
      • 3 attempts (default)
      • connect timeout   = 8 s
      • read timeout      = 60 s       <-- longer than before
    """
    if url in HTML_CACHE:
        return HTML_CACHE[url]

    for attempt in range(1, tries + 1):
        try:
            r = SESSION.get(url,
                            headers=HDRS,
                            timeout=(connect_t, read_t),
                            allow_redirects=True)
            r.raise_for_status()
            HTML_CACHE[url] = r.text
            return r.text

        except (requests.Timeout,
                requests.exceptions.ReadTimeout) as e:

            dbg("GET-TIMEOUT", f"{url}  (try {attempt}/{tries})")
            if attempt == tries:          # give up
                HTML_CACHE[url] = ""
                return ""

            time.sleep(2 ** attempt)      # 2 s, 4 s back-off and retry
            continue

        except requests.HTTPError as e:
            dbg("GET-ERR",
                f"{url[-60:]} → HTTP {e.response.status_code}")
            HTML_CACHE[url] = ""
            return ""

    # should never reach here
    HTML_CACHE[url] = ""
    return ""

# ─── ESTER utilities ────────────────────────────────────────────────
def _ester_fields(rec):
    soup=BeautifulSoup(_download(rec),"html.parser")
    ttl=soup.select_one("h1.title, h2.title") \
        or soup.select_one("td#bibTitle") \
        or soup.select_one("td.bibInfoLabel:-soup-contains('Pealkiri')+td.bibInfoData")
    aut=soup.select_one("td.bibInfoLabel:-soup-contains('Autor')+td.bibInfoData")
    return (strip_ctrl(ttl.get_text(" ",strip=True)) if ttl else "",
            strip_ctrl(aut.get_text(" ",strip=True)) if aut else "")

_NONBOOK_TAGS = (
    "videosalvestis", "dvd", "blu-ray",
    "cd-plaat", "audiofile", "helisalvestis",
    # feel free to extend when something new slips through
)

def _is_nonbook(rec_url: str) -> bool:
    """
    True  ⇢  the record is a physical *non-book* carrier (DVD, CD, …)
    False ⇢  looks like a book
    """
    html = _download(rec_url).lower()
    return any(tag in html for tag in _NONBOOK_TAGS)

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

    (Uses `ERS_CACHE` for memoisation.)
    """
    if rec_url in ERS_CACHE:             # memoised result → instant
        return ERS_CACHE[rec_url]

    html = _download(rec_url)             # your existing cached GET
    soup = BeautifulSoup(html, 'html.parser')

    has_physical = bool(
        soup.select_one("tr.bibItemsEntry, tr[class*=bibItemsEntry]")
    )
    if has_physical:
        ERS_CACHE[rec_url] = False
        return False

    page_lc = html.lower()
    eres    = any(tag.lower() in page_lc for tag in _ERS_TAGS)
    ERS_CACHE[rec_url] = eres
    return eres

# ---------------------------------------------------------------------
# _looks_like_same_book – new body with Slavic-name canonicalisation
# ---------------------------------------------------------------------
def _looks_like_same_book(w_ttl: str, w_aut: str, rec_url: str) -> bool:
    """
    Decide whether *rec_url* describes the same book as (*w_ttl*, *w_aut*).

    Strategy
    --------
    • Title  → every token must be present; for 1-word titles the record
               title must *start with* that word (after ASCII-folding) or
               be identical.
    • Author → compare canonicalised surname codes.
    """
    # 1. pull record title / author ----------------------------------
    r_ttl, r_aut = _ester_fields(rec_url)
    if not r_ttl:                         # fetch or parse failed
        return False

    # 2. tokenise ----------------------------------------------------
    wanted_toks = _tokenise(strip_parens(w_ttl))
    record_toks = _tokenise(r_ttl) | _tokenise(r_aut)

    # ---- TITLE test ------------------------------------------------
    if not wanted_toks:
        ttl_ok = True                    # empty → cannot test

    elif len(wanted_toks) > 1:
        # multi-word title → wanted tokens must be *subset* of record tokens
        ttl_ok = wanted_toks <= record_toks

    else:                                # single-word title (e.g. “Dune”)
        import re
        word     = next(iter(wanted_toks))          # the only token
        rec_fold = _ascii_fold(r_ttl).lstrip()       # ASCII-folded record
        # match start-of-string  word + (space / punctuation / end)
        ttl_ok   = bool(re.match(rf'^{re.escape(word)}(\W|$)', rec_fold))

    # ---- AUTHOR test -----------------------------------------------
    surname_raw   = _surname(w_aut)
    surname_parts = _tokenise(surname_raw)

    wanted_canon  = {_canon_name(p) for p in surname_parts}
    record_canon  = {_canon_name(t) for t in record_toks}

    auth_ok = (not surname_parts) or wanted_canon <= record_canon

    # ---- VERBOSE dump ----------------------------------------------
    if DEBUG:
        print(f"┌─  title/author comparator ──────────────────────────────────────")
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
        verdict = "MATCH" if (ttl_ok and auth_ok) else "SKIP"
        colour  = "grn"  if verdict == "MATCH" else "red"
        print(f"└─  verdict: {CLR[colour]}{verdict}{CLR['reset']}\n")

    return ttl_ok and auth_ok

# ──────────────────────────────────────────────────────────────────────
# ❶  Scrape one HTML holdings page
def _scrape_holdings_html(url: str) -> list[tuple[str, str, str]]:
    dbg("holdings", f"HTML→ {url}")
    html   = _download(url)

    soup   = BeautifulSoup(html, "html.parser")
    rows   = soup.select("#tab-copies tr[class*='bibItemsEntry'], "
                         ".additionalCopies tr[class*='bibItemsEntry']")
    out: list[tuple[str, str, str]] = []
    for r in rows:
        tds = r.find_all("td")
        if len(tds) >= 3:
            loc   = strip_ctrl(tds[0].get_text()).strip()
            call  = strip_ctrl(tds[1].get_text()).strip() if len(tds) > 2 else ""
            sta   = strip_ctrl(tds[2].get_text()).strip().upper()
            out.append((loc, call, sta))

    dbg("holdings", f"{len(out)} rows matched selector")
    if DEBUG and not out:
        dbg("holdings", "      saving HTML preview")
        with open("debug_empty_holdings.html", "w", encoding="utf-8") as fh:
            fh.write(html[:1200])            # write only first 1 200 B

    N = 2
    if DEBUG and out:
        for loc, call, sta in out[:N]:
            dbg("holdings", f"{loc[:38]:38} {call[:16]:16} {sta}")
        if len(out) > N:
            dbg("holdings", f"... (+{len(out) - N} more)")

    return out

# ──────────────────────────────────────────────────────────────────────
# ❷  Ask EPiK JSON endpoint
def _copies_via_api(bib: str) -> list[tuple[str, str, str]]:
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

    out: list[tuple[str, str, str]] = []
    for it in items:
        loc  = it.get("libraryNameEst") or it.get("libraryName") or ""
        sta  = (it.get("statusEst") or it.get("status") or "").upper()
        call = (it.get("callNumber") or it.get("callNo") or it.get("kohaviit") or "").strip()
        out.append((strip_ctrl(loc), strip_ctrl(call), strip_ctrl(sta)))

    if DEBUG and out:
        loc, call, sta = out[0]
        dbg("holdings", f"{loc[:38]:38} {call[:16]:16} {sta}")
        if len(out) > 1:
            loc, call, sta = out[1]
            dbg("holdings", f"{loc[:38]:38} {call[:16]:16} {sta}")

    return out

# ──────────────────────────────────────────────────────────────────────
# ❸  Master helper
def holdings(rec: str) -> list[tuple[str, str, str]]:
    """
    ① fetch …/holdings~   → parse
    ② fetch …/holdingsa~  → parse
    ③ EPiK JSON API       → parse
    returns [(location, KOHAVIIT, STATUS), …]
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

def safe_id(raw: str) -> str:
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
    if slug in ID_SEEN:
        base, n = slug, 2
        while f"{base}-{n}" in ID_SEEN:
            n += 1
        slug = f"{base}-{n}"
    ID_SEEN.add(slug)
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

_MIN_BYTES = 1337 # Google placeholder image is about 10.5KB

# ────────────────────────────────────────────────────────────────────
#  write_covers_page  –  wider tiles, caption under the jacket
# ────────────────────────────────────────────────────────────────────
def write_covers_page(outfile: str = "all_covers.html") -> None:
    """
    Build an HTML gallery – one <figure> per book, cover on top.
    """
    log("ℹ", "Writing cover gallery page", "cyan")

    gallery: list[tuple[str, str, str]] = []  # (surname-key, title-key, brief)
    seen: set[str] = set()

    for (author, title), rec_url in RECORD_URL.items():
        gr_author, gr_title = GR_META.get(rec_url, (author, title))
        brief = record_brief(
            rec_url,
            f"{gr_author} – {gr_title}",
            isbn_hint = RECORD_ISBN.get(rec_url, ""),
            gr_author = gr_author,
            gr_title  = gr_title
        )
        if brief in seen:
            continue
        seen.add(brief)
        gallery.append((_surname(gr_author), gr_title.lower(), brief))

    if not gallery:
        return

    gallery.sort()  # by surname → title

    IMG_RE = re.compile(r"<img[^>]+>", re.I)

    def split_brief(snippet: str) -> tuple[str, str]:
        m = IMG_RE.search(snippet)
        if m:
            img = m.group(0)
            caption = snippet.replace(img, "", 1)
        else:
            img, caption = "", snippet
        return img, caption

    with open(outfile, "w", encoding="utf-8") as fh:
        fh.write(
            "<!doctype html>\n<meta charset='utf-8'>\n"
            "<title>Goodreads → ESTER – kaanekogu</title>\n"
            "<style>\n"
            " body{font-family:sans-serif;margin:1.4rem;}\n"
            " h1{margin:.2rem 0 1.2rem;font-size:1.8rem;}\n"
            " .grid{display:grid;gap:1.6rem;"
            "       grid-template-columns:repeat(auto-fit,minmax(240px,1fr));}\n"
            " figure{margin:0;display:flex;flex-direction:column;"
            "        align-items:center;border:1px solid #ccc;"
            "        padding:.8rem;border-radius:.5rem;background:#fafafa;"
            "        box-shadow:0 2px 4px rgba(0,0,0,.08);}\n"
            " figure img{height:220px;max-width:100%;object-fit:contain;"
            "            margin-bottom:.8rem;}\n"
            " figcaption{font-size:.9rem;line-height:1.3rem;text-align:center;}\n"
            " a{text-decoration:none;color:#035;}"
            " a:hover{text-decoration:underline;}\n"
            "</style>\n"
            "<h1>Kogu kaanekogu</h1>\n"
            "<section class='grid'>\n"
        )
        for _sk, _tk, brief in gallery:
            img_html, caption_html = split_brief(brief)
            fh.write("  <figure>")
            fh.write(img_html or
                     "<div style='height:220px;display:flex;"
                     "justify-content:center;align-items:center;"
                     "color:#666;font-size:.8rem;'>– no cover –</div>")
            fh.write(f"<figcaption>{caption_html}</figcaption></figure>\n")
        fh.write("</section>")
    log('✓', f"[Done] {outfile}", 'grn')


# ── helper: remove every "(…)" segment anywhere in the string ───────
_PARENS = re.compile(r"\s*\([^)]*\)")
def strip_any_parens(s: str) -> str:
    return _PARENS.sub(" ", s).strip()

# ── tiny helper used later ------------------------------------------
def split_disp(disp: str) -> tuple[str, str]:
    """
    Split Goodreads-style “Author – Title …” → (author, title_without_x)
    Also removes the trailing “ (3×)” copy counter that build_map() adds.
    """
    if " – " in disp:
        author, title = disp.split(" – ", 1)
    else:
        author, title = "", disp

    # strip the “ (n×)” tail that may be present
    title = re.sub(r"\s+\(\d+×\)$", "", title)
    return author.strip(), title.strip()


# ---------------------------------------------------------------------------
#  smarter cover hunt  –  FINAL (drop-in) VERSION
# ---------------------------------------------------------------------------
def _find_cover(
    soup: BeautifulSoup,
    *,
    author: str = "",
    title:  str = "",
    isbn_hint: str = ""
) -> str:
    """
    Return a usable cover-image URL or "".

    • Updates   COVER_SRC[label]   and   BOOKS_WITH_COVER.
    • Silently ignores the Google-Books placeholder (a dull “no cover” tile)
      which is   books.google.com/books/content … printsec=frontcover …
    """

    # ── bookkeeping helper ──────────────────────────────────────────
    def _mark(src_label: str) -> None:
        global BOOKS_WITH_COVER
        COVER_SRC[src_label] += 1
        BOOKS_WITH_COVER    += 1

    tried: list[tuple[str, str]] = []          # (URL, verdict)

    # ── generic URL tester --------------------------------------------------
    def _try(label: str, urls: list[str]) -> str:
        """
        Iterate through *urls* and accept the first usable image.
        Every attempt is recorded in *tried* for DEBUG dumps.
        """
        for u in urls:
            verdict = "skip"
            try:
                r    = requests.get(u, stream=True, timeout=5,
                                    allow_redirects=True)
                ct   = r.headers.get("Content-Type", "")
                size = int(r.headers.get("Content-Length", "0") or 0)

                # ——  ✂️  Google-Books placeholder guard  ✂️  ————————————
                #  Empirically:
                #    • real covers   → image/jpeg, invariably contain  "&edge="
                #    • placeholder   → image/png  (sometimes JPEG)  **no edge**
                #                      tiny < 15 kB
                if ("books.google.com/books/content" in u
                        and "&edge=" not in u
                        and size < 15_000):
                    verdict = f"gbooks-placeholder {size} B"
                    tried.append((u, f"{label}: {verdict}"))
                    continue                        # look at next candidate
                # ------------------------------------------------------------------

                if r.ok and ct.startswith("image") and size >= _MIN_BYTES:
                    verdict = f"OK ({size/1024:.1f} kB)"
                    tried.append((u, f"{label}: {verdict}"))
                    _mark(label)
                    return r.url                   # <-- winner!

                verdict = f"{ct or 'no-CT'} {size} B"

            except Exception as e:
                verdict = f"ERR {e.__class__.__name__}"

            finally:
                tried.append((u, f"{label}: {verdict}"))

        return ""                                 # nothing usable in *urls*

    # ────────────────────────────────────────────────────────────────
    #  0. inline <img>  +  og:image
    # ────────────────────────────────────────────────────────────────
    urls0 = []
    for tag in soup.select("img, noscript img"):
        for attr in IMG_ATTRS:
            src = (tag.get(attr) or "").strip()
            if _looks_like_jacket(src):
                urls0.append(_abs(src))

    og = (soup.find("meta", property="og:image")
          or soup.find("meta", attrs={"name": "og:image"}))
    if og and _looks_like_jacket(og.get("content", "")):
        urls0.append(_abs(og["content"]))

    if (hit := _try("inline/og", urls0)):
        dbg("cover-pick", hit)
        return hit

    # ────────────────────────────────────────────────────────────────
    #  1. EPiK avalanche / IIIF
    # ────────────────────────────────────────────────────────────────
    code_m = (re.search(r'record=([b\d]+)', str(soup)) or
              re.search(r'catalog/([b\d]+)', str(soup)) or
              re.search(r'"code"\s*:\s*"([b\d]+)"', str(soup)))
    if code_m:
        code  = code_m.group(1)
        urls1 = [f"https://www.ester.ee/iiif/2/{code}/full/500,/0/default.jpg"]

        try:                                   # one avalanche JSON call
            js = requests.post(
                    "https://epik.ester.ee/api/data/getImagesByCodeList",
                    json=[code], timeout=8).json()[0]

            if js.get("imageData"):            # inline base-64
                b64 = js["imageData"]
                if (len(b64) > 300_000 and
                        (js.get("urlLarge") or js.get("urlSmall"))):
                    urls1.append(js.get("urlLarge") or js.get("urlSmall"))
                else:
                    _mark("avalanche/inline")
                    dbg("cover-pick", "inline base-64")
                    return "data:image/jpeg;base64," + b64

            urls1.append(js.get("urlLarge") or js.get("urlSmall") or "")

        except Exception:
            pass

        if (hit := _try("avalanche/iiif", urls1)):
            dbg("cover-pick", hit)
            return hit

    # ────────────────────────────────────────────────────────────────
    #  2. Google-Books thumbnail  (ISBN)
    # ────────────────────────────────────────────────────────────────
    isbn_list = _scrape_isbns(soup) or ([isbn_hint] if isbn_hint else [])
    urls2 = [_GOOGLE.format(i) for i in isbn_list]
    if (hit := _try("gbooks", urls2)):
        dbg("cover-pick", hit)
        return hit

    # ────────────────────────────────────────────────────────────────
    #  3. OpenLibrary  (ISBN)
    # ────────────────────────────────────────────────────────────────
    urls3 = [_OPENLIB.format(i) for i in isbn_list]
    if (hit := _try("openlib", urls3)):
        dbg("cover-pick", hit)
        return hit

    # ────────────────────────────────────────────────────────────────
    #  4. Google-Images fallback
    # ────────────────────────────────────────────────────────────────
    # q = f"{author} {title} book cover".strip()
    clean_author = strip_any_parens(author)
    clean_title  = strip_any_parens(title)
    q = f"{clean_author} {clean_title}".strip()

    dbg("cover-pick", f"Google Images search: {q!r}")
    if (gimg := _first_google_image(q)):
        if (hit := _try("gimages", [gimg])):
            dbg("cover-pick", hit)
            return hit

    # ── nothing worked ------------------------------------------------
    dbg("cover-pick", "EMPTY")
    if DEBUG:
        for url, verdict in tried:
            print(f"   • {verdict:32} → {url}")
    return ""

# ────────────────────────────────────────────────────────────────────
def record_brief(
    rec,
    fallback_title: str = "",
    *,
    isbn_hint: str = "",
    isbn: str | None = None,

    # always arrive from process_title()
    gr_author: str | None = None,
    gr_title : str | None = None,

    **_ignored                 # swallow anything else silently
) -> str:
    """
    Build the one-liner used in pop-ups and the cover gallery.

    • Always call _find_cover() with the *cleanest* strings available
      (prefer Goodreads over catalogue).
    • Accepts both old and new signatures.
    """

    # --- alias normalisation ----------------------------------------
    if isbn and not isbn_hint:
        isbn_hint = isbn

    soup: BeautifulSoup | None = None
    url : str | None           = None

    # --- parse the record page (if a URL was supplied) --------------
    if hasattr(rec, "select_one"):                      # BeautifulSoup / Tag
        soup = rec if isinstance(rec, BeautifulSoup) else BeautifulSoup(str(rec), "html.parser")

    elif isinstance(rec, str):
        if rec.startswith("http"):                      # URL
            url = rec
            if url in BRIEF_CACHE:                     # memoised
                return BRIEF_CACHE[url]
            soup = BeautifulSoup(_download(url), "html.parser")
        else:                                           # raw HTML blob
            soup = BeautifulSoup(rec, "html.parser")

    # --- extract author/title from the record page ------------------
    cat_title = cat_author = ""
    if soup:
        ttl_el = soup.select_one(".bibInfoData strong") \
              or soup.select_one("h1.title, h2.title, td#bibTitle")
        aut_el = soup.select_one(".bibInfoData a[href*='/author']") \
              or soup.select_one("td.bibInfoLabel:-soup-contains('Autor')+td.bibInfoData")
        cat_title  = ttl_el.get_text(" ", strip=True) if ttl_el else ""
        cat_author = aut_el.get_text(" ", strip=True) if aut_el else ""

    # --- choose the *clean* strings we’ll give to Google ------------
    # prefer Goodreads; fall back to catalogue; last resort = fallback_title
    nice_author = (gr_author or cat_author).strip()
    nice_title  = (gr_title  or cat_title
                   or (fallback_title.split(" – ", 1)[1] if " – " in fallback_title else fallback_title)
                   or "—").strip()

    # --- try to fetch a cover ---------------------------------------
    cover = ""
    if soup:
        cover = _find_cover(soup=soup,
                            author=nice_author,
                            title=nice_title,
                            isbn_hint=isbn_hint)

    if not cover and isbn_hint:
        cover = openlib_link(isbn_hint, "M")            # OpenLibrary fallback

    cover_html = (
        f'<img src="{cover}" loading="lazy" '
        f'style="height:120px;float:right;margin-left:.6em;" '
        f'onerror="this.remove();">'
        if cover else ""
    )

    # --- compose final fragment -------------------------------------
    link_start = f'<a href="{html.escape(url)}" target="_blank" rel="noopener noreferrer">' if url else ""
    link_end   = "</a>" if url else ""

    text = (f"{html.escape(nice_author)} – <em>{html.escape(nice_title)}</em>"
            if nice_author else f"<em>{html.escape(nice_title)}</em>")

    brief = f"{cover_html}{link_start}{text}{link_end}"

    if url:
        BRIEF_CACHE[url] = brief

    return brief

_JS_SNIPPET = r"""
<style>
/* ─── top-left search control ───────────────────────────────────── */
.searchbox{
  position:relative;margin:4px 0 0 4px;padding:2px 4px;
  background:#fff;border:1px solid #999;border-radius:4px;
  box-shadow:0 1px 4px rgba(0,0,0,.25);z-index:1001;
}
.searchbox input{
  border:0;outline:none;width:200px;font:13px sans-serif;
}

/* ─── pop-up list of titles ─────────────────────────────────────── */
.leaflet-popup-content{
  max-width:1600px;
  overflow-y:auto;          /* vertical scroll if needed         */
  overflow-x:hidden;        /* never show horizontal scrollbar   */
}
.leaflet-popup-content ul{
  margin:6px 0 0;
  padding-left:18px;
  padding-right:4em;      /* invisible gutter for bold titles  */
}
.leaflet-popup-content li{cursor:pointer;color:#06c;}
.leaflet-popup-content li.sel{font-weight:bold;color:#000;}

/* ─── fixed side panel (“Valitud raamatud”) ─────────────────────── */
#selectionBox{
  position:fixed;top:1rem;right:1rem;z-index:9999;
  max-width:340px;max-height:90vh;overflow:auto;
  background:#fff;border:2px solid #444;padding:.5rem 1rem;
  box-shadow:0 0 8px rgba(0,0,0,.3);font-size:.9em;
}
#selectionBox p{
  margin:.4em 0;line-height:1.25em;clear:both;
}
#selectionBox hr{
  clear:both;margin:.4em 0;height:0;border:0;
}
</style>

<script>
(() => {
/* helpers */
const   $ = s => document.querySelector(s);
const  $$ = s => [...document.querySelectorAll(s)];
const esc = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

/* side-panel (unchanged) */
const picked = new Map();
function header(on){
  return (on?'<button onclick="clr()" style="float:right;font:bold 18px/14px sans-serif;border:0;background:#eee;cursor:pointer">&times;</button>':'')
       +  '<h3 style="margin:0;font:16px sans-serif">Valitud raamatud</h3>';
}
function refresh(){
  const box = $('#selectionBox'); if(!box) return;
  box.innerHTML = header(picked.size) +
    [...picked.values()].map(t=>`<p>${t}</p>`).join('<hr style="margin:.4em 0">');
}
window.clr = () => { picked.clear(); $$('.sel').forEach(li=>li.classList.remove('sel')); refresh(); };
window.toggleBook = id => {
  const li = document.getElementById(id); if(!li) return;
  if(picked.has(id)){ picked.delete(id); li.classList.remove('sel'); }
  else              { picked.set(id, li.dataset.brief.replace(/&amp;/g,'&')); li.classList.add('sel'); }
  refresh();
};

/* colour palette */
const colourFor = n => n===1 ? 'red' : n<=3 ? 'orange' : n<=7 ? 'beige' : 'green';

/* main installer */
function install(map){
  /* side panel skeleton */
  if(!$('#selectionBox')){
    const d=document.createElement('div'); d.id='selectionBox'; d.innerHTML=header(false);
    document.body.appendChild(d);
  }

  /* search control */
  const ctl = L.control({position:'topleft'});
  ctl.onAdd = () => {
    const div=L.DomUtil.create('div','searchbox');
    div.innerHTML='<input id="mapSearch" placeholder="otsi pop-up nimekirjast">';
    return div;
  };
  ctl.addTo(map);
  const inp = $('#mapSearch');
  L.DomEvent.disableClickPropagation(inp);

  /* collect markers */
  const libMarkers = new Map();            // slug → marker
  map.eachLayer(l=>{
    if(l instanceof L.Marker && l.options.libSlug){
      libMarkers.set(l.options.libSlug, l);
      /* cache entries array for quick matching */
      l._entries = (l.options.searchText||'').split('||');
    }
  });

  /* filter routine */
  function applyFilter(){
    const rx = inp.value ? new RegExp(esc(inp.value.trim()),'i') : null;

    /* 1. hide/show individual <li> when a popup is open */
    $$('li[data-brief]').forEach(li=>{
      li.style.display = (!rx || rx.test(li.textContent)) ? '' : 'none';
    });

    /* 2. per-library match count from cached titles */
    libMarkers.forEach((marker, slug)=>{
      const n = rx
        ? marker._entries.filter(t => rx.test(t)).length
        : marker.options.totalCount;

      /* hide or show the marker */
      if(n===0){
        if(map.hasLayer(marker)) map.removeLayer(marker);
      }else{
        if(!map.hasLayer(marker)) map.addLayer(marker);
        marker.setIcon(
          L.AwesomeMarkers.icon({icon:'book',prefix:'fa',markerColor:colourFor(n)})
        );
      }

      /* update counter in open popup */
      if(marker.isPopupOpen && marker.isPopupOpen()){
        const pop = marker.getPopup();
        const el  = pop.getElement();
        if(el){
          const span = el.querySelector('.hitCount');
          if(span) span.textContent = `(${n} pealkirja)`;
        }
        /* ── NEW: force Leaflet to resize the box ── */
        if(pop.update){                 // Leaflet ≥ 1.9
          pop.update();                 // public method
        }else if(pop._updateLayout){    // older Leaflet
          pop._updateLayout();
          pop._updatePosition();
        }
      }
    });
  }

  inp.addEventListener('input', applyFilter);
  map.on('popupopen', applyFilter);
  applyFilter();              // first run
}

/* wait for Folium’s map */
function wait(){
  for(const k in window){
    const v = window[k];
    if(v && v instanceof L.Map){ install(v); return; }
  }
  setTimeout(wait,40);
}
window.addEventListener('load', wait);
})();
</script>
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
def probe(label: str, term: str, url: str = "") -> list[str]:
    # 1. crawl & collect ----------------------------------------------------
    links = collect_record_links(url, limit=4)
    hits  = len(links)

    # 2. colour: green if we found anything, red otherwise -----------------
    colour = "grn" if hits else "red"

    # 3. single-line summary -----------------------------------------------
    log("🔍", f"{label:<14} {term:<30} → {hits} hit{'s' if hits!=1 else ''}",
        colour)

    # 4. verbose URL (keep in dim so it’s easy to spot if you need it) ------
    dbg("↳", url)

    return links

def by_isbn(isbn):
    url = (f"{SEARCH}/X?searchtype=X&searcharg={isbn}"
           "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return probe("keyword-isbn", isbn, url)

def by_title_index(t, *, _label="title-idx"):
    enc  = ester_enc(norm_dash(t))
    url  = (f"{SEARCH}/X?searchtype=t&searcharg="
            f"{urllib.parse.quote_plus(enc, safe='{}')}"
            "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return probe(_label, t, url)

def by_keyword(a, t, *, _label="keyword-ttl"):
    raw = squeeze(f"{a} {t}")
    enc = ester_enc(norm_dash(raw))
    url = (f"{SEARCH}/X?searchtype=X&searcharg="
           f"{urllib.parse.quote_plus(enc, safe='{}')}"
           "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
    return probe(_label, raw, url)

def search(author: str, title: str, isbn: str) -> list[str]:
    """
    Return the first ESTER record whose title & author really match
    the Goodreads entry.  Strategy:

      1. ISBN probe
      2. title-index probe
      3. keyword  “author title”
      4. keyword  “title”
    """
    title = strip_parens(title)           # normalise once up-front

    # ① ISBN ----------------------------------------------------------------
    if isbn:
        for rec in by_isbn(isbn):
            return [rec]                  # ISBN is unique → accept

    # helper: run a probe function and yield only *matching* records
    def _candidates(fn, *args, _label):
        for rec in fn(*args, _label=_label):
            if _looks_like_same_book(title, author, rec):
                yield rec

    # ②–④ probes ------------------------------------------------------------
    probes = (
        (by_title_index,            (title,),          "title-idx"),
        (by_keyword,      (author,  title),            "kw-author+title"),
        (by_keyword,      ("",      title),            "kw-title-only"),
    )
    for fn, args, lbl in probes:
        for rec in _candidates(fn, *args, _label=lbl):
            return [rec]                # first convincing hit

    return []                           # nothing passed the comparator

def openlib_link(isbn13: str, size: str = "M") -> str:
    # size = S | M | L   – whatever you prefer
    return (
        f"https://covers.openlibrary.org/b/isbn/{isbn13}-{size}.jpg"
        "?default=false"          # << *** key change  ***
    )   

# ----------------------------------------------------------------------
# worker: process one Goodreads entry  (✓ now passes clean strings down)
# ----------------------------------------------------------------------
def process_title(idx: int, total: int,
                  author: str, title: str, isbn: str
                  ) -> tuple[Counter, dict]:
    """
    • Log progress for the *idx/total*-th Goodreads entry
    • Locate *one* matching ESTER record (if any)
    • Collect the number of holdings whose status string contains “KOHAL”
    • Return:
        copies  – Counter keyed by (author, title, "lib|addr") → count
        meta    – { "lib|addr" → (pretty_library_name, address) }

    Side-effects
    ------------
    • Populates RECORD_URL, RECORD_ISBN, GR_META
    • Populates CALLNUMS[(author, title, key)] with list of kohaviit strings
    • Appends to NOT_FOUND / NO_KOHAL
    """
    global NOT_FOUND, NO_KOHAL

    t0 = time.time()
    log(f"[{idx:3}/{total}]", f"{author} – {title}", "cyan")

    copies: Counter = Counter()
    meta:   dict    = {}

    # ── ①  look for a matching record on ESTER ──────────────────────
    recs = search(author, title, isbn)

    if not recs:
        log("✗", "no matching record on ESTER", "red")
        line = f"{author} – {title}" + (f" (ISBN {isbn})" if isbn else "")
        NOT_FOUND.append(line)
        log("⏳", f"{time.time() - t0:.2f}s", "pur")
        return copies, meta

    rec = recs[0]
    RECORD_URL[(author, title)] = rec
    RECORD_ISBN[rec]            = isbn or ""
    GR_META[rec]                = (author, title)

    record_brief(
        rec,
        fallback_title=f"{author} – {title}",
        isbn_hint      = isbn or "",
        gr_author      = author,
        gr_title       = title
    )

    # ── ②  scrape holdings → count “KOHAL” copies + collect KOHAVIIT ─
    for loc, call, status in holdings(rec):
        name, addr = resolve(loc)
        key        = f"{name}|{addr}"

        if "KOHAL" in status:
            copies[(author, title, key)] += 1
            if call:
                CALLNUMS[(author, title, key)].append(call)

        meta[key] = (name, addr)

    tot = sum(copies.values())

    if tot == 0:
        log("✗", "0 × KOHAL", "red")
        line = f"{author} – {title}" + (f" (ISBN {isbn})" if isbn else "")
        NO_KOHAL.append(line)
    else:
        log("✓", f"{tot} × KOHAL", "grn")

    log("⏳", f"{time.time() - t0:.2f}s", "pur")
    return copies, meta

# ─── map builder ─────────────────────────────────────────────────────
def build_map(lib_books: dict, meta: dict, coords: dict, outfile) -> None:
    """
    lib_books { key → [(display, url), …] }   display = “Author – Title …”
    meta      { key → (pretty_library_name, address) }
    coords    { key → (lat, lon) }
    """
    if not coords:
        log("!", "Nothing available (KOHAL) on ESTER", "yel", err=True)
        return

    log("ℹ", "Writing map page", "cyan")

    # ── centre roughly on mean lat/lon ──────────────────────────────
    lat0 = sum(la for la, _ in coords.values()) / len(coords)
    lon0 = sum(lo for _, lo in coords.values()) / len(coords)

    m = folium.Map(location=(lat0, lon0), zoom_start=13)
    folium.Element("<style>.leaflet-popup-content{max-width:1600px;}</style>").add_to(m)
    m.get_root().html.add_child(folium.Element(_JS_SNIPPET))

    for key, entries in lib_books.items():
        if key not in coords:
            continue

        lat, lon = coords[key]
        lib_name, _addr = meta[key]
        slug = safe_id(lib_name)

        # sort titles by ASCII-folded surname
        def _sort_key(e): return _surname(e[0].split("–", 1)[0].strip())
        entries_sorted = sorted(entries, key=_sort_key)

        # build <li> list + plain-text corpus
        lis, corpus = [], []
        for disp, est_url in entries_sorted:
            auth, titl = split_disp(disp)
            isbn_hint  = RECORD_ISBN.get(est_url, "")
            tag_prefix = dual_link(auth, titl, ester=est_url, isbn=isbn_hint) + " "

            if est_url:
                gr_author, gr_title = GR_META.get(est_url, ("", ""))
                brief_html = (tag_prefix +
                              record_brief(est_url, disp,
                                           isbn_hint=isbn_hint,
                                           gr_author=gr_author,
                                           gr_title=gr_title))
            else:
                brief_html = tag_prefix + html.escape(disp)

            # ── NEW: append kohaviit list for this (book, library) ───
            calls = CALLNUMS.get((auth, titl, key), [])
            if calls:
                unique_calls = sorted(set(calls))
                brief_html += ("<br><small><b>Kohaviit:</b> " +
                               ", ".join(html.escape(c) for c in unique_calls) +
                               "</small>")

            brief_attr = (brief_html
                          .replace("&",  "&amp;")
                          .replace('"', "&quot;")
                          .replace("'", "&#39;"))
            elem_id = safe_id(lib_name + disp)

            lis.append(
                f'<li id="{elem_id}" data-brief="{brief_attr}" '
                f'data-lib="{slug}" '
                f'style="cursor:pointer;color:#06c;" '
                f'onclick="event.stopPropagation();toggleBook(\'{elem_id}\')">'
                f'{html.escape(disp)}</li>'
            )
            corpus.append(disp)

        popup_html = (
            f"<div style='{POPUP_CSS}' data-lib='{slug}'>"
            f"<b>{html.escape(lib_name)}</b> "
            f"<span class='hitCount' style='color:#666;font-size:90%;'>"
            f"({len(entries_sorted)} pealkirja)</span>"
            f"<div id='popupContent'><ul>{''.join(lis)}</ul></div></div>"
        )

        icon = folium.Icon(color=pcol(len(entries_sorted)), icon="book", prefix="fa")
        folium.Marker(
            location=(lat, lon),
            popup=folium.Popup(popup_html, max_width=1600, min_width=300),
            icon=icon,
            libSlug=slug,
            searchText="||".join(corpus),
            totalCount=len(entries_sorted)
        ).add_to(m)

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

    log("Hello, Goodreader, my old friend - I’ve come to scrape with you again…")

    t0 = time.time()

    titles=gd_csv(a.goodreads_csv,a.max_titles) if a.goodreads_csv \
          else parse_web_shelf(a.goodreads_user,a.max_titles)
    log(f"Found {len(titles)} titles")

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
    else:
        log('✓', f"[Done]", 'grn')
    
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

    if NOT_FOUND:
        log("\n=== TITLES **NOT FOUND** ON ESTER ===", "", "red")
        for line in NOT_FOUND:
            log("✗", line, "red")
        log(f"Total not-found: {len(NOT_FOUND)}", "", "red")

    if NO_KOHAL:
        log("\n=== TITLES FOUND, BUT WITH **NO KOHAL COPIES** ===", "", "yel")
        for line in NO_KOHAL:
            log("•", line, "yel")
        log(f"Total no-KOHAL: {len(NO_KOHAL)}", "", "yel")

    build_map(lib_books,meta,coords,a.output)

    write_covers_page("all_covers.html")

     # ── cover statistics ───────────────────────────────────────────
    if BOOKS_WITH_COVER:
        log("ℹ", f"Covers found: {BOOKS_WITH_COVER}/{len(titles)}", "cyan")
        for src, n in COVER_SRC.most_common():
            pct = n * 100 / BOOKS_WITH_COVER
            log("•", f"{src:<15} {n:3}  ({pct:4.1f} %)", "dim")
    else:
        log("ℹ", "No covers were extracted", "yel")

    total_time = time.time() - t0
    log("⏱", f"Total time spent: {total_time:.2f}s", "yel")

if __name__=="__main__":
    main()
