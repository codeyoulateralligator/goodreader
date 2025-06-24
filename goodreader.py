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
    m=re.search(r"\b(b\d{7})",rec)
    if not m: return []
    bib=m.group(1)
    soup=BeautifulSoup(_download(f"{ESTER}/search~S8*est?/.{bib}/.{bib}/1,1,1,B/"
                                 f"holdings~{bib}&FF=&1,0,/indexsort=-"),"html.parser")
    rows=soup.select("#tab-copies tr[class*='bibItemsEntry'], "
                     ".additionalCopies tr[class*='bibItemsEntry']")
    out=[]
    for r in rows:
        tds=r.find_all("td")
        if len(tds)<3: continue
        if "KOHAL" not in strip_ctrl(tds[2].get_text()).upper(): continue
        out.append(strip_ctrl(tds[0].get_text()).strip())
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

# ─── id / brief helpers ──────────────────────────────────────────────
_id_re=re.compile(r"\W+")
def _safe_id(s): return _id_re.sub("",s)[:40] or "x"
def _record_brief(url: str, fallback: str = "") -> str:
    """
    Return a short HTML snippet for the book’s card.
    • If the record page cannot be fetched (rate-limit, etc.),
      fall back to *fallback* (plain text).
    """
    try:
        html = _download(url)
        soup = BeautifulSoup(html, "html.parser")

        ttl = soup.select_one("h1.title, h2.title")
        aut = soup.select_one(
            "td.bibInfoLabel:-soup-contains('Autor') + td.bibInfoData")
        pub = soup.select_one(
            "td.bibInfoLabel:-soup-contains('Ilmunud') + td.bibInfoData")

        parts = []
        if ttl: parts.append(f"<b>{htm.escape(ttl.get_text(strip=True))}</b>")
        if aut: parts.append(htm.escape(aut.get_text(strip=True)))
        if pub: parts.append(htm.escape(pub.get_text(strip=True)))

        return "<br>".join(parts) + \
               f'<br><a href="{url}" target="_blank">ESTER →</a>'

    except Exception as ex:         # 429, network error, …
        if DEBUG:
            log("!", f"_record_brief fail {url} ({ex})", "yel", err=True)
        return htm.escape(fallback or url)

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
           .map(txt => "<p>"+txt+"</p>")
           .join("");
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
def process_title(idx,total,a,t,isbn):
    t0=time.time()
    log(f"[{idx:3}/{total}]",f"{a} – {t}","cyan")
    log("🔖 ISBN:",isbn or "— none —","pur")
    copies=Counter(); meta={}
    recs=search(a,t,isbn); rec=recs[0] if recs else None
    if rec and _looks_like_same_book(t,a,rec):
        RECORD_URL[(a,t)]=rec; _record_brief(rec,f"{a} – {t}")
        for loc in holdings(rec):
            name,addr=resolve(loc); key=f"{name}|{addr}"
            copies[(a,t,key)]+=1; meta[key]=(name,addr)
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

            brief_html = _record_brief(url, disp) if url else htm.escape(disp)
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
