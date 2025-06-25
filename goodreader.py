#!/usr/bin/env python3
"""
goodreads_ester_mapper.py 🇪🇪📚
Build b-32 • 2025-07-02
"""

from __future__ import annotations
# ── stdlib ───────────────────────────────────────────────────────────
import argparse, csv, json, os, pathlib, re, sys, time, unicodedata, urllib.parse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, List, Tuple
# ── third-party ──────────────────────────────────────────────────────
import requests, folium, html as htm
from bs4 import BeautifulSoup
from geopy.geocoders import Nominatim
from geopy.extra.rate_limiter import RateLimiter
from requests.exceptions import ReadTimeout
import hashlib
from html import unescape


# ─── debug helpers ───────────────────────────────────────────────────
DEBUG = bool(int(os.getenv("ESTER_DEBUG", "0")))
CLR = {k: f"\x1b[{v}m" for k, v in dict(dim=90, cyan=36, yel=33,
                                         grn=32, red=31, pur=35, reset=0).items()}
_WHITES = re.compile(r"\s{2,}")
def log(tag, msg, col="dim", err=False):
    stream = sys.stderr if err or DEBUG else sys.stdout
    print(f"{CLR[col]}{tag}{CLR['reset']} {msg}", file=stream, flush=True)
def dbg(msg):                          # very verbose HTTP trace
    if DEBUG: log("•", msg, "red")

FAILED: List[str] = []                 # titles with zero *KOHAL*
HTML_CACHE: dict[str, str] = {}
RECORD_URL: dict[tuple[str, str], str] = {}
RECORD_BRIEF: dict[str, str] = {}
RECORD_ISBN: dict[str, str] = {}       # record-url  →  isbn13
_BRIEF_CACHE: dict[str, str] = {} 
_ID_SEEN: set[str] = set()

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
def parse_web_shelf(uid:str, limit:int|None):
    out=[]; page=1
    while True:
        url=(f"{GOODREADS_SHELF}/{uid}?shelf=to-read&per_page=200&page={page}"
             "&sort=date_added&view=table")
        soup=BeautifulSoup(_download(url),"html.parser")
        rows=soup.select("tr[id^='review_']")
        if not rows: break
        for r in rows:
            a=r.select_one("td.field.author a")
            t=r.select_one("td.field.title a")
            raw=(r.select_one("td.field.isbn13") or "").get_text(strip=True)
            m=re.search(r"(\d{13})",raw); isbn=m.group(1) if m else ""
            if a and t: out.append((a.get_text(strip=True),t.get_text(strip=True),isbn))
            if limit and len(out)>=limit: return out
        if soup.select_one("a:-soup-contains('next »')"): page+=1
        else: break
    return out

# ─── tokenisers / surname helper ─────────────────────────────────────
_norm_re=re.compile(r"[^a-z0-9]+")
def _ascii_fold(s): return unicodedata.normalize("NFKD",s).encode("ascii","ignore").decode("ascii").lower()
def _tokenise(s):   return {tok for tok in _norm_re.split(_ascii_fold(s)) if tok}
def _surname(a):    # supports “Lastname, Firstname”
    if "," in a: return _ascii_fold(a.split(",",1)[0]).split()[0]
    p=_ascii_fold(a).split(); return p[-1] if p else ""

# ─── HTTP download (cached) ──────────────────────────────────────────
SESSION = requests.Session()
def _download(url:str)->str:
    if url in HTML_CACHE: return HTML_CACHE[url]
    dbg(f"GET {url}")
    try: r=SESSION.get(url,headers=HDRS,timeout=TIMEOUT)
    except ReadTimeout: r=SESSION.get(url,headers=HDRS,timeout=TIMEOUT)
    r.raise_for_status(); HTML_CACHE[url]=r.text
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

def _is_eresource(rec):
    page=_download(rec).lower()
    return any(w in page for w in ("võrguteavik","võrguressurss","veebiteavik","e-ressursid"))

def _first_candidate_link(html,base):
    soup=BeautifulSoup(html,"html.parser")
    a=soup.select_one("a[href*='/record=b']") or soup.select_one("h2.title > a[href*='frameset']")
    return urllib.parse.urljoin(base,a["href"]) if a else None

def collect_record_links(url):
    html=_download(url); cand=_first_candidate_link(html,url)
    if not cand: return []
    if "frameset" in cand:
        cand=_first_candidate_link(_download(cand),cand) or cand
    if _is_eresource(cand):
        nxt=BeautifulSoup(html,"html.parser").select("a[href*='/record=b']")
        if len(nxt)>1: cand=urllib.parse.urljoin(url,nxt[1]["href"])
    return [cand]

def _looks_like_same_book(w_ttl,w_aut,rec):
    w_ttl=strip_parens(w_ttl); r_ttl,r_aut=_ester_fields(rec)
    if not r_ttl: return False
    sur=_surname(w_aut)
    ok=len((_tokenise(r_ttl)|_tokenise(r_aut)) & _tokenise(w_ttl)) >= max(1,len(_tokenise(w_ttl))//2)
    if sur and sur not in (_tokenise(r_ttl)|_tokenise(r_aut)): ok=False
    color = "\x1b[32m" if ok else "\x1b[31m"
    status = f"{color}{'match' if ok else 'skip'}\x1b[0m"
    print(f"\x1b[37m{w_ttl!r} vs {r_ttl!r} → {status}\x1b[0m")
    return ok

def holdings(rec):
    m = re.search(r"\b(b\d{7})", rec)
    if not m:
        return []

    bib  = m.group(1)
    soup = BeautifulSoup(
        _download(f"{ESTER}/search~S8*est?/.{bib}/.{bib}/1,1,1,B/"
                  f"holdings~{bib}&FF=&1,0,/indexsort=-"),
        "html.parser"
    )

    rows = soup.select("#tab-copies tr[class*='bibItemsEntry'], "
                       ".additionalCopies tr[class*='bibItemsEntry']")

    out = []
    for r in rows:
        tds = r.find_all("td")
        if len(tds) < 3:
            continue
        loc    = strip_ctrl(tds[0].get_text()).strip()
        status = strip_ctrl(tds[2].get_text()).strip().upper()
        out.append((loc, status))        # ← return BOTH columns
    return out

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

# ----------------------------------------------------------------------
# Low-level helper – talks to the hidden “avalanche” REST endpoint
# ----------------------------------------------------------------------
def _avalanche_cover(recnum: str, session: requests.Session | None = None) -> str:
    """
    Ask the avalanche micro-service for cover art of one ESTER record.

    Parameters
    ----------
    recnum   ESTER record number, e.g. "b2404042".
    session  optional requests.Session for connection reuse.

    Returns
    -------
    The best image URL (or a data:-URI) or "" if not available.
    """
    api = "https://epik.ester.ee/ester/avalanche?ids"
    sess = session or requests

    try:
        resp = sess.post(api, json=[recnum], timeout=10)
        resp.raise_for_status()
        meta = resp.json()[0]           # we asked for one record → list[0]
        print(meta)
        if meta.get("imageData"):       # base-64 payload
            return f"data:image/jpeg;base64,{meta['imageData']}"

        return meta.get("urlLarge") or meta.get("urlSmall") or ""
    except Exception:
        # network problems, JSON errors, etc. – pretend nothing was found
        return ""
    
_BAD_IMG_PAT = re.compile(r'(?i)(/screens/|spinner|transparent\.gif|\.svg$)')
_GOOGLE      = "https://books.google.com/books/content?vid=ISBN{0}&printsec=frontcover&img=1&zoom=1"
_OPENLIB     = "https://covers.openlibrary.org/b/isbn/{0}-M.jpg"
IMG_ATTRS    = ("data-src", "data-original", "data-large", "data-iiif-high", "src")

def _looks_like_jacket(src: str) -> bool:
    return (
        src
        and (src.startswith(("http://", "https://", "/iiif/")) or src.startswith("data:image/"))
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

def _first_good_url(urls: list[str]) -> str:
    for u in urls:
        dbg(f"Trying URL: {u}")
        try:
            # Cloudinary: HEAD → 404, but GET (no body) → 302 → 200
            r = requests.get(u, stream=True, timeout=5, allow_redirects=True)
            ct = r.headers.get("Content-Type", "")
            dbg(f"GET {u} → {r.status_code} ({ct})")
            if r.ok and ct.startswith("image"):
                dbg(f"Selected image URL: {r.url}")
                return r.url                       # r.url == final location
        except Exception as e:
            dbg(f"Exception for URL {u}: {e}")
    dbg("No good image URL found.")
    return ""

def _via_search_thumb(code: str) -> str:
    """Return the cover thumb that appears only in the search-results page."""
    url = f"https://www.ester.ee/search~S8*est/X?searchtype=X&searcharg={code}"
    print(f"search-thumb URL: {url}")

    try:
        soup = BeautifulSoup(requests.get(url, timeout=8).text, "html.parser")

        img = soup.select_one("td.briefcitPhotos img[src]")
        if not img:
            print("search-thumb: no <img> found")
            return ""

        src = img["src"]
        if not src.startswith(("http://", "https://")):
            src = f"https://www.ester.ee{src}"     # make absolute

        print(f"search-thumb candidate: {src}")
        return src if _first_good_url([src]) else ""
    except Exception as e:
        print(f"search-thumb error: {e}")
        return ""
# ---------------------------------------------------------------------------

def _find_cover(soup: BeautifulSoup) -> str:
    # STEP 1 ─ look at what’s already in the HTML ---------------------------
    for tag in soup.select("img, noscript img"):
        for attr in IMG_ATTRS:
            if (src := tag.get(attr) or "").strip() and _looks_like_jacket(src):
                return _abs(src)

    og = soup.find("meta", property="og:image") or soup.find("meta", attrs={"name": "og:image"})
    if og and _looks_like_jacket(og.get("content", "")):
        return _abs(og["content"])

    # STEP 2 ─ EPiK API (+ fallbacks) --------------------------------------
    html = str(soup)
    m = (
        re.search(r'record=([b\d]+)', html)
        or re.search(r'catalog/([b\d]+)', html)
        or re.search(r'"code"\s*:\s*"([b\d]+)"', html)
    )
    if not m:
        return ""

    code = m.group(1)
    api  = "https://epik.ester.ee/api/data/getImagesByCodeList"
    try:
        item = requests.post(api, json=[code], timeout=10).json()[0]
    except Exception:
        item = None

    # 2a – inline base-64
    if item and item.get("imageData"):
        return "data:image/jpeg;base64," + item["imageData"]

    # 2b – IIIF (try record-code *before* uuid)
    iiif_code = f"https://www.ester.ee/iiif/2/{code}/full/500,/0/default.jpg"
    if _first_good_url([iiif_code]):
        return iiif_code      # ✅ works for list thumbs and often for full cover

    # 2c – IIIF with UUID (rarely used nowadays)
    uuid = item and item.get("idUuid")
    if uuid:
        iiif_uuid = f"https://epik.ester.ee/iiif/2/{uuid}/full/500,/0/default.jpg"
        if _first_good_url([iiif_uuid]):
            return iiif_uuid

    # 2c – Google Books / Open Library by ISBN
    isbn_urls = [
        _GOOGLE.format(i) for i in _scrape_isbns(soup)
    ] + [
        _OPENLIB.format(i) for i in _scrape_isbns(soup)
    ]
    return _first_good_url(isbn_urls)


def _record_brief(rec, fallback_title: str = "", isbn: str = "") -> str:
    """
    Build a one-liner HTML snippet for the map pop-up.

    `rec` may be:
        • BeautifulSoup Tag / Soup
        • raw HTML string
        • record URL (str)
    """
    # --- 1. Retrieve / parse -------------------------------------------------
    soup: BeautifulSoup | None = None
    url: str | None = None

    if hasattr(rec, "select_one"):          # Tag / Soup
        soup = rec if isinstance(rec, BeautifulSoup) else BeautifulSoup(str(rec), "html.parser")

    elif isinstance(rec, str):
        if rec.startswith("http"):          # a link – maybe cached already
            url = rec
            if url in _BRIEF_CACHE:
                return _BRIEF_CACHE[url]

            html = _download(url)
            soup = BeautifulSoup(html, "html.parser")
        else:                               # raw HTML
            soup = BeautifulSoup(rec, "html.parser")

    # --- 2. Extract bits -----------------------------------------------------
    title = author = ""

    if soup:
        ttl_el = (
            soup.select_one(".bibInfoData strong")
            or soup.select_one("h1.title, h2.title, td#bibTitle")
        )
        aut_el = (
            soup.select_one(".bibInfoData a[href*='/author']")
            or soup.select_one("td.bibInfoLabel:-soup-contains('Autor')+td.bibInfoData")
        )

        title  = ttl_el.get_text(strip=True) if ttl_el else ""
        author = aut_el.get_text(strip=True) if aut_el else ""

    # graceful fall-backs
    if not title:
        # fallback_title is something like "Author – Title" → keep only title part
        if " – " in fallback_title:
            title = fallback_title.split(" – ", 1)[1]
        else:
            title = fallback_title or "—"

    # --- 3. Cover hunt -------------------------------------------------------
    cover = _find_cover(soup) if soup else ""
    if not cover and isbn:
        cover = _openlib_link(isbn, "M")    # OpenLibrary, if it exists

    cover_html = f'<img src="{cover}" style="height:120px;float:right;margin-left:.6em;">' if cover else ""

    # ── 4. Compose & cache ────────────────────────────────
    link_start = f'<a href="{htm.escape(url)}" target="_blank" rel="noopener noreferrer">' if url else ""
    link_end   = '</a>' if url else ""

    if author:
        text  = f"{htm.escape(author)} – <em>{htm.escape(title)}</em>"
    else:
        text  = f"<em>{htm.escape(title)}</em>"

    brief = f"{cover_html}{link_start}{text}{link_end}"

    if url:
        _BRIEF_CACHE[url] = brief
    return brief

_JS_SNIPPET = """
<script>
/* turn "&lt;br&gt;" etc. back into real tags */
function decodeHTML(str){
  const t   = document.createElement('textarea');
  t.innerHTML = str;
  return t.value;
}

const chosen = new Map();

function toggleBook(id){
  const li    = document.getElementById(id);
  const panel = document.getElementById("selectionBox");

  if(chosen.has(id)){
    chosen.delete(id);
    li.style.fontWeight = "normal";
  }else{
    chosen.set(id, decodeHTML(li.dataset.brief));
    li.style.fontWeight = "bold";
  }

  panel.innerHTML =
  "<h3>Valitud raamatud</h3>" +
  Array.from(chosen.values())
    .map(txt => "<p>" + txt + "</p>")
    .join("<hr style='margin:.4em 0;'>");
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
<div id="selectionBox"><h3>Valitud raamatud</h3></div>
"""

# ─── search helpers ──────────────────────────────────────────────────
def _probe(label,url):
    links=collect_record_links(url); hits=len(links)
    log("🛰 probe",f"{label:<11} {hits} hit(s)","grn" if hits else "red")
    if not hits: log("⋯",url,"dim")
    return links
def by_isbn(isbn): return _probe("keyword-isbn",f"{SEARCH}/X?searchtype=X&searcharg={isbn}"
                                               "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
def by_title_index(t):
    q=ester_enc(norm_dash(t))
    return _probe("title-idx",f"{SEARCH}/X?searchtype=t&searcharg="
                              f"{urllib.parse.quote_plus(q,safe='{}')}"
                              "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
def by_keyword(a,t):
    raw=squeeze(f"{a} {t}"); q=ester_enc(norm_dash(raw))
    return _probe("keyword-ttl",f"{SEARCH}/X?searchtype=X&searcharg="
                                f"{urllib.parse.quote_plus(q,safe='{}')}"
                                "&searchscope=8&SORT=DZ&extended=0&SUBMIT=OTSI")
def search(a,t,isbn):
    t=strip_parens(t)
    for fn,arg in ((by_isbn,isbn),(by_title_index,t),(by_keyword,(a,t)),(by_keyword,("",t))):
        if not arg: continue
        links=fn(*arg) if isinstance(arg,tuple) else fn(arg)
        if links: return links
    return []

# ─── worker ──────────────────────────────────────────────────────────
def _openlib_link(isbn13: str, size: str = "M") -> str:
    # size = S | M | L   – whatever you prefer
    return (
        f"https://covers.openlibrary.org/b/isbn/{isbn13}-{size}.jpg"
        "?default=false"          # << *** key change  ***
    )   

def process_title(idx,total,a,t,isbn):
    t0=time.time()
    log(f"[{idx:3}/{total}]",f"{a} – {t}","cyan")
    log("🔖 ISBN:",isbn or "— none —","pur")
    copies=Counter(); meta={}
    recs=search(a,t,isbn); rec=recs[0] if recs else None
    if rec and _looks_like_same_book(t,a,rec):
        RECORD_URL[(a,t)] = rec
        RECORD_ISBN[rec] = isbn or ""
        _record_brief(rec, f"{a} – {t}", isbn or "")
        for loc, status in holdings(rec):
                name, addr = resolve(loc)
                key        = f"{name}|{addr}"

                # availability count for the pin colour
                if "KOHAL" in status:
                    copies[(a, t, key)] += 1

                meta[key] = (name, addr)

                # NEW — echo every copy line to the console
                dbg("•", f"{loc}\t{status}", "dim")
    tot=sum(copies.values())
    log("✓" if tot else "✗",f"{tot} × KOHAL" if tot else "0 × KOHAL",
        "grn" if tot else "red")
    if not tot: FAILED.append(f"{a} – {t}"+(f" (ISBN {isbn})" if isbn else ""))
    log("⏳",f"{time.time()-t0:.2f}s","pur")
    return copies,meta

# ─── map builder ─────────────────────────────────────────────────────
# ─── map builder ----------------------------------------------------
def build_map(lib_books, meta, coords, outfile):
    """
    lib_books { key → [(display, url)  OR  display_string, …] }
    meta      { key → (nice_name, address) }
    coords    { key → (lat, lon) }
    """
    if not coords:
        log("!", "Nothing available (KOHAL) on ESTER", "yel", err=True)
        return

    # centre map on mean lat / lon
    lats = [la for la, _ in coords.values()]
    lons = [lo for _, lo in coords.values()]
    centre = (sum(lats) / len(lats), sum(lons) / len(lons))

    m = folium.Map(location=centre, zoom_start=11)
    folium.Element(
        "<style>.leaflet-popup-content{max-width:1600px;}</style>"
    ).add_to(m)

    # IMPORTANT: add JS/CSS into the document <head>,
    # so the functions are visible from every popup
    m.get_root().html.add_child(folium.Element(_JS_SNIPPET))

    for key, entries in lib_books.items():
        if key not in coords:
            continue
        lat, lon = coords[key]
        name, _  = meta[key]

        lis: list[str] = []
        for entry in entries:
            # accept either ("disp", url) tuples or bare strings
            if isinstance(entry, (tuple, list)):
                disp, url = entry[0], (entry[1] if len(entry) > 1 else "")
            else:
                disp, url = entry, ""

            elem_id = _safe_id(name + disp)

            brief_html = _record_brief(url, disp, RECORD_ISBN.get(url, "")) if url else htm.escape(disp)
            # escape for HTML attribute (keep <br> etc. un-escaped)
            brief_attr = (brief_html.replace("&", "&amp;")
                                      .replace('"', "&quot;")
                                      .replace("'", "&#39;"))

            lis.append(
                f'<li id="{elem_id}" data-brief="{brief_attr}" '
                f'style="cursor:pointer;color:#06c;" '
                f'onclick="event.stopPropagation();toggleBook(\'{elem_id}\')">'
                f'{htm.escape(disp)}</li>'
            )

        html_popup = (
            f"<div style='{POPUP_CSS}'>"
            f"<b>{htm.escape(name)}</b><ul>"
            + "".join(lis) +
            "</ul></div>"
        )

        folium.Marker(
            location=[lat, lon],
            popup=folium.Popup(html_popup, max_width=1600, min_width=300),
            icon=folium.Icon(color=pcol(len(entries)), icon="book", prefix="fa"),
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

if __name__=="__main__":
    main()
