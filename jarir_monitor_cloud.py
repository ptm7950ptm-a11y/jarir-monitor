#!/usr/bin/env python3
# discount_monitor.py
# Monitors Jarir (jarir.com, Arabic) discount listings, shows a Windows
# notification for new offers and opens the best ones in Firefox.
# The results page has a "جديد" inbox at the top (new offers + price drops) that stays
# until you open the offer or press "تم الاطلاع على الكل".
#
# v2 adds two sections for products that are OUT of stock online (see "Out-of-stock offers" in the settings):
#   - "كمية قليلة في المعارض": the site's own showroom stock API says at least one showroom has some (notification)
#   - "غير متوفر في أي مكان": no showroom has stock, strong discount (results page only: phone the showroom)
#
#   python discount_monitor.py            -> run forever
#   python discount_monitor.py --once     -> one scan, then stop        (add --cats 10001,10002 for a quick test)
#   python discount_monitor.py --check 683540 -> which showrooms have stock of one item number
#   python discount_monitor.py --dump     -> save page 1 of every site to ./dump/ (for debugging)
#   python discount_monitor.py --test FILE -> offline parser test on a saved page

import base64
import datetime
import html as htmllib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
import webbrowser
from pathlib import Path

try:                                        # optional: only the Chrome fallback needs them
    import undetected_chromedriver as uc
    from selenium.common.exceptions import TimeoutException
    uc.Chrome.__del__ = lambda self: None
except ImportError:
    uc = None

    class TimeoutException(Exception):
        pass

# ----------------------------- Settings -----------------------------
PAGES = 20                      # pages per site (84 items each on Landmark sites)
PAGE_TIMEOUT_SEC = 90           # the pages are ~7 MB, so allow time before giving up
READY_WAIT_SEC = 40             # extra time to wait for the product data to be complete
CHECK_EVERY_MIN = 30            # minutes between full scans
MIN_DISCOUNT_PCT = 75           # notifications + the starting value of the filter on the results page
COLLECT_MIN_PCT = 1             # everything with at least this discount is collected; filter it on the results page
JARIR_MAX_PAGES = 1000          # Jarir: max requests (or scroll loads) per category per scan
JARIR_API_PAGE_SIZE = 40        # Jarir API: products per request (the site itself uses 12; falls back to 12 if refused)
JARIR_BROWSER_FALLBACK = os.environ.get("JARIR_BROWSER_FALLBACK", "1") == "1"   # if the plain API request is refused, scan with Chrome instead
IMG_WIDTH = 400                 # product image width on the results page (small = fast)
IMG_QUALITY = 70
OPEN_IN_BROWSER = not os.environ.get("CI")          # open the results page in the browser below
BROWSER = "firefox"             # "firefox" | "default"
FIREFOX_PATHS = [
    r"C:\Program Files\Mozilla Firefox\firefox.exe",
    r"C:\Program Files (x86)\Mozilla Firefox\firefox.exe",
]
HISTORY_HOURS = 24              # offers stay on the results page this long (unread ones too)
PAGE_REFRESH_SEC = 60           # the open results page reloads itself

HERE = Path(__file__).resolve().parent
DATA = Path(os.environ["DATA_DIR"]) if os.environ.get("DATA_DIR") else HERE
DATA.mkdir(parents=True, exist_ok=True)
NTFY_TOPIC = os.environ.get("NTFY_TOPIC", "")      # ntfy.sh topic for phone notifications
STATE_FILE = DATA / "discount_seen_jarir_v2.json"
LOG_FILE = DATA / "discount_new_offers_jarir_v2.log"
HISTORY_FILE = DATA / "discount_found_jarir_v2.json"
HTML_FILE = DATA / "offers_jarir.html"
DUMP_DIR = DATA / "dump_jarir_v2"

# ---- Out-of-stock offers (v2): items NOT in stock online, checked against the showroom stock API ----
SHOWROOM_MIN_PCT = 30           # "limited quantity in a showroom": minimum discount (results page + notification)
UNAVAIL_MIN_PCT = 50            # "unavailable everywhere": minimum discount (results page only - phone the showroom)
SHOWROOM_CITIES = []            # [] = every Saudi city; or e.g. ["RUH"] / ["RUH", "JED"] (Jarir's city codes)
SHOWROOM_MAX_CHECKS = 400       # max products checked against the showroom API per scan
SHOWROOM_MAX_VARIANTS = 3       # colours / sizes checked per product
SHOWROOM_CACHE_MIN = 120        # a checked item is not asked again for this many minutes
SHOWROOM_API = "https://www.jarir.com/api/v2/sa_ar/stock/getAvailableShowrooms?sku={sku}&countryId=181"
SHOWROOM_FILE = DATA / "showroom_found.json"
SHOWROOM_CACHE_FILE = DATA / "showroom_cache.json"

SITES = [
    # name, base url, listing url template, parser kind
    # Jarir (Nuxt site). Tested behaviour of the server:
    #   works:  ...?jb_discount_percentage=1-99[&sort=price]   (a filtered list)
    #   fails (CF_5xx):  any URL with &page=N, custom discount ranges (50-99, 75-99)
    # The category is opened WITHOUT filters; only the first 12 products come from the URL, the rest
    # are loaded by scrolling (the site uses infinite scroll). Discount filtering is done afterwards,
    # on the results page (and MIN_DISCOUNT_PCT for notifications).
    # To collect more Jarir categories, copy this entry, change the "name" and the category .html part,
    # and add "store": "Jarir" so the same product is shown only once.
    {"name": "Jarir", "base": "https://www.jarir.com", "kind": "jarir",
     "url": "https://www.jarir.com/computer-supplies-x.html",
     "url_alt": "https://www.jarir.com/computer-supplies-x.html?sort=price",
     # No-browser mode: category codes read from Jarir's public product API (the same one the page
     # calls while scrolling). These are ALL the top-level categories = the whole shop.
     # Remove codes you do not want (e.g. "10006" books is by far the biggest) to make a scan shorter.
     "api_categories": ["4", "5", "11", "1651", "10001", "10002", "10003", "10004", "10005",
                        "10006", "10007", "10008"]},
]

MIN_PCT_BY_SITE = {s["name"]: s.get("min_pct", MIN_DISCOUNT_PCT) for s in SITES}

# Category slugs (substring match) to exclude
EXCLUDE_CATEGORY_PARTS = [
    "watches", "makeup", "fragrance", "lunchessentials", "lunchbag", "lunchbox",
]
# Words to exclude from product titles live in excluded_words.txt (one word or phrase per line).
# The file is created on first run and re-read at the start of every scan, so you can edit it while the script runs.
EXCLUDED_WORDS_FILE = HERE / "excluded_words.txt"
DEFAULT_EXCLUDED_WORDS = [
    "ساعة", "ساعات", "مكياج", "عطر", "عطور", "أحمر شفاه",
    "حقيبة غداء", "شنطة غداء", "صندوق غداء", "علبة غداء",
    "وسادة", "شنطة", "صحن", "مرآة", "ستائر", "طاولة", "كرسي", "مصباح",
    "صندل", "بلوزة", "فستان", "حاوية", "لمبة", "شرشف", "مرتبة", "كنبة",
]
_EXCLUDED_NORM = []


def norm(text: str) -> str:
    """Make Arabic spelling variants match: أ/إ/آ->ا, ة->ه, ى->ي, drop diacritics and tatweel."""
    text = re.sub("[\u064B-\u0652\u0640]", "", text or "")
    for a, b in (("أ", "ا"), ("إ", "ا"), ("آ", "ا"), ("ٱ", "ا"), ("ة", "ه"), ("ى", "ي")):
        text = text.replace(a, b)
    return text.lower().strip()


def reload_excluded_words():
    global _EXCLUDED_NORM
    if not EXCLUDED_WORDS_FILE.exists():
        EXCLUDED_WORDS_FILE.write_text(
            "# One word or phrase per line. Lines starting with # are ignored.\n"
            + "\n".join(DEFAULT_EXCLUDED_WORDS) + "\n", encoding="utf-8")
    lines = EXCLUDED_WORDS_FILE.read_text(encoding="utf-8-sig").splitlines()
    _EXCLUDED_NORM = [norm(l) for l in lines if l.strip() and not l.strip().startswith("#")]


reload_excluded_words()


# ----------------------------- Parsing ------------------------------
def is_excluded(title: str, cats: str = "") -> bool:
    cats = cats.lower()
    if any(p in cats for p in EXCLUDE_CATEGORY_PARTS):
        return True
    t = norm(title)
    return any(w in t for w in _EXCLUDED_NORM)


def make_offer(site, pid, title, price, was, url, brand="", img=""):
    try:
        price, was = float(price), float(was)
    except (TypeError, ValueError):
        return None
    if not price or was <= price:
        return None
    return {"id": f"{site['name']}:{pid}", "site": site["name"], "store": site.get("store", site["name"]),
            "title": title, "brand": brand,
            "price": price, "was": was, "pct": round((was - price) / was * 100), "url": url, "img": img}


def page_has_data(src, site=None):
    """True once the data script is complete (a cut-off page has no closing tag):
    __NEXT_DATA__ for the Landmark sites, __NUXT_DATA__ for Jarir."""
    tag = "__NUXT_DATA__" if (site or {}).get("kind") == "jarir" else "__NEXT_DATA__"
    return bool(re.search(r'<script[^>]*id="%s"[^>]*>.*?</script>' % tag, src or "", re.S))


def parse_landmark(site, page_source):
    try:
        return _parse_landmark(site, page_source)
    except (ValueError, KeyError, TypeError):    # truncated / changed page -> treated as a failed page
        return None


def _parse_landmark(site, page_source):
    """Landmark Group sites (Centrepoint, Splash, Max, Home Centre, Homebox):
    products are embedded as base64 JSON inside __NEXT_DATA__."""
    m = re.search(r'<script id="__NEXT_DATA__" type="application/json">(.*?)</script>', page_source, re.S)
    if not m:
        return None
    data = json.loads(m.group(1))
    state = json.loads(base64.b64decode(data["props"]["initialState"]))
    hits = state["algoliaProductReducer"]["data"]["hits"]
    out = []
    for h in hits:
        if not h.get("inStock", 1):
            continue
        if is_excluded(h.get("title", ""), " ".join(h.get("allCategories") or [])):
            continue
        u = h.get("url", "")
        url = site["base"] + "/sa/ar" + u if u.startswith("/") else u
        o = make_offer(site, h.get("pid") or h.get("sku"), h.get("title", ""),
                       h.get("price"), h.get("wasPrice"), url, h.get("brand", ""),
                       h.get("thumb_image") or h.get("thumbnailImg") or "")
        if o:
            out.append(o)
    return out, len(hits)


def _unflatten_nuxt(arr):
    """Rebuild the object graph of a Nuxt __NUXT_DATA__ payload (devalue format: a flat list where
    every value is an index into that list; negative numbers are undefined/null/NaN/Infinity)."""
    cache = {}

    def res(i):
        if not isinstance(i, int) or isinstance(i, bool):
            return i
        if i < 0:
            return None
        if i in cache:
            return cache[i]
        v = arr[i]
        if isinstance(v, list):
            tag = v[0] if v and isinstance(v[0], str) else None
            if tag in ("Reactive", "ShallowReactive", "Ref", "ShallowRef"):
                r = res(v[1])
                cache[i] = r
                return r
            if tag in ("EmptyRef", "EmptyShallowRef", "null", "undefined"):
                return None
            if tag in ("Set", "Map"):
                r = []
                cache[i] = r
                r.extend(res(x) for x in v[1:])
                return r
            if tag in ("Date", "BigInt", "RegExp", "URL"):
                return res(v[1]) if len(v) > 1 else None
            r = []
            cache[i] = r
            r.extend(res(x) for x in v)
            return r
        if isinstance(v, dict):
            r = {}
            cache[i] = r
            for k, x in v.items():
                r[k] = res(x)
            return r
        return v

    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, 20000))
    try:
        return res(1)           # index 0 is the ShallowReactive wrapper, index 1 is the root
    finally:
        sys.setrecursionlimit(old)


def parse_jarir(site, page_source):
    try:
        return _parse_jarir(site, page_source)
    except (ValueError, KeyError, TypeError, IndexError, AttributeError):   # truncated / changed page
        return None


def _parse_jarir(site, page_source):
    """Jarir (Nuxt): the product list is in the __NUXT_DATA__ payload, in the vue-query cache
    entry 'category-products' (Elasticsearch-style hits, one cache page per fetched page)."""
    m = re.search(r'<script[^>]*id="__NUXT_DATA__"[^>]*>(.*?)</script>', page_source, re.S)
    if not m:
        return None
    root = _unflatten_nuxt(json.loads(m.group(1)))
    queries = root["state"]["$svue-query-state"]["queries"]
    hits = []
    for q in queries:
        key = q.get("queryKey") or []
        if key and key[0] == "category-products":
            for pg in (q["state"]["data"] or {}).get("pages") or []:
                hits += pg["data"]["hits"]["hits"]
    out = _jarir_offers(site, [h.get("_source") or {} for h in hits])
    return out, len(hits)


def _flag_off(v):
    return str(v) in ("0", "False", "false")


def _online_in_stock(x):
    """In stock online = the product itself OR any of its variants is. (A multi-colour product can say 0 on its
    main record while a colour is available - v1 dropped those.)"""
    kids = x.get("configurable_children") or []
    if any(not _flag_off(c.get("is_stock_available", 1)) for c in kids):
        return True
    return not _flag_off(x.get("is_stock_available", 1))


def _jarir_unavailable(site, sources):
    """Discounted products that are NOT in stock online (they are checked later against the showroom stock API)."""
    out = []
    floor = min(SHOWROOM_MIN_PCT, UNAVAIL_MIN_PCT)
    for x in sources:
        if _online_in_stock(x):
            continue
        title = x.get("name") or x.get("meta_title") or ""
        if is_excluded(title):
            continue
        kids = x.get("configurable_children") or []
        best = None
        for y in [x] + list(kids):
            try:
                was = float(y.get("regular_price") or y.get("price") or 0)
                price = float(y.get("final_price") or y.get("special_price") or 0)
            except (TypeError, ValueError):
                continue
            if was > price > 0:
                pct = (was - price) / was * 100
                if best is None or pct > best[0]:
                    best = (pct, price, was)
        if best is None or round(best[0]) < floor:
            continue
        key = x.get("url_path") or ((x.get("url_key") or "") + ".html")
        url = key if key.startswith("http") else site["base"] + "/" + key.lstrip("/")
        o = make_offer(site, x.get("sku") or x.get("id"), title, best[1], best[2], url, x.get("brand", ""),
                       x.get("image") or x.get("small_image") or "")
        if not o:
            continue
        if kids:
            skus = {str(k.get("sku")): (k.get("cofa") or k.get("jarir_colo") or "") for k in kids if k.get("sku")}
        else:
            skus = {str(x.get("sku") or x.get("id")): ""}
        o["skus"] = list(skus.items())[:SHOWROOM_MAX_VARIANTS]
        out.append(o)
    return out


def _jarir_offers(site, sources):
    """sources = the '_source' dicts of Jarir's products (from the page data or from the live page)."""
    out = []
    for x in sources:
        if not _online_in_stock(x):
            continue
        title = x.get("name") or x.get("meta_title") or ""
        if is_excluded(title):
            continue
        key = x.get("url_path") or ((x.get("url_key") or "") + ".html")
        url = key if key.startswith("http") else site["base"] + "/" + key.lstrip("/")
        o = make_offer(site, x.get("sku") or x.get("id"), title,
                       x.get("final_price") or x.get("special_price"),
                       x.get("regular_price") or x.get("price"),
                       url, x.get("brand", ""), x.get("image") or x.get("small_image") or "")
        if o:
            out.append(o)
    return out


def parse(site, page_source):
    if site.get("kind") == "jarir":
        return parse_jarir(site, page_source)
    return parse_landmark(site, page_source)


# ----------------------------- Results page -------------------------
def small_img(url):
    """Ask the image CDN (Amplience) for a small, compressed version instead of the 2100px original."""
    if not url:
        return ""
    if "jarir.com" in url:      # Jarir's image host does not take the Amplience parameters
        return url
    return url.split("?")[0] + f"?w={IMG_WIDTH}&qlt={IMG_QUALITY}&fmt=auto"


def dedupe_key(o):
    """Colour/size variants of one product are separate ids but look identical on the page."""
    return (o.get("store", o["site"]), o["title"].strip(), o["price"], o["was"])


def unique(offers):
    seen, out = set(), []
    for o in offers:
        k = dedupe_key(o)
        if k not in seen:
            seen.add(k)
            out.append(o)
    return out


def load_history():
    try:
        return json.loads(HISTORY_FILE.read_text(encoding="utf-8")) if HISTORY_FILE.exists() else []
    except Exception:
        return []


PAGE_TEMPLATE = r"""<!DOCTYPE html>
<html lang="ar" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="refresh" content="__REFRESH__">
<title>العروض الجديدة</title>
<style>
*{box-sizing:border-box}
body{margin:0;font-family:Tahoma,Arial,sans-serif;background:#f4f4f4;color:#222}
header{padding:14px 20px;background:#fff;border-bottom:1px solid #ddd;position:sticky;top:0;z-index:5}
header small{color:#777;margin-inline-start:10px}
#inbox{margin:14px 14px 0;background:#fff;border:2px solid #0a8f3c;border-radius:10px;padding:10px 12px}
.ih{display:flex;gap:10px;align-items:center;flex-wrap:wrap;margin-bottom:8px}
.ih h2{font-size:16px;margin:0;color:#0a8f3c}
.ih small{color:#777}
.ih button,.ih select{padding:5px 12px;border:1px solid #0a8f3c;border-radius:8px;background:#fff;color:#0a8f3c;font:inherit;font-size:13px;cursor:pointer}
.ih button{margin-inline-start:auto}.ih button:hover{background:#0a8f3c;color:#fff}
.strip{display:flex;gap:10px;overflow-x:auto;padding-bottom:6px}
.strip .card{flex:0 0 170px}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:14px;padding:16px}
.card{background:#fff;border-radius:6px;overflow:hidden;text-decoration:none;color:inherit;box-shadow:0 1px 3px #0002;display:block}
.card:hover{box-shadow:0 2px 10px #0003}
.im{position:relative;aspect-ratio:3/4;background:#eee}
.im img{width:100%;height:100%;object-fit:cover;display:block}
.site{position:absolute;top:8px;inset-inline-start:8px;background:#000b;color:#fff;font-size:12px;padding:2px 8px;border-radius:10px}
.bds{position:absolute;bottom:6px;inset-inline-start:6px;display:flex;gap:4px;flex-wrap:wrap}
.bd2{font-size:11px;padding:1px 7px;border-radius:10px;color:#fff}
.bd2.new{background:#0a8f3c}.bd2.drop{background:#d96a00}
.bd{padding:10px 12px}
.pr{display:flex;gap:8px;align-items:baseline;flex-wrap:wrap}
.pr b{font-size:20px;color:#c00}.pr s{color:#888;font-size:14px}
.off{background:#c00;color:#fff;font-size:12px;padding:1px 6px;border-radius:3px}
.br{color:#666;font-size:13px;margin-top:6px;min-height:16px}.tt{font-size:14px;margin-top:2px;line-height:1.4}
.tm{color:#aaa;font-size:11px;margin-top:6px}
.x{position:absolute;top:6px;inset-inline-end:6px;width:26px;height:26px;border:0;border-radius:50%;background:#000a;color:#fff;font-size:14px;line-height:26px;padding:0;cursor:pointer;z-index:2}
.x:hover{background:#c00}
#unhide{margin-inline-start:12px;padding:3px 10px;border:1px solid #999;border-radius:8px;background:#fff;color:#555;font:inherit;font-size:12px;cursor:pointer}
#unhide:hover{background:#eee}
.mp{margin-inline-start:14px;font-size:13px;color:#555}.mp select{padding:3px 8px;font:inherit;border:1px solid #999;border-radius:6px;background:#fff}
#more{display:block;margin:18px auto;padding:9px 26px;border:1px solid #999;border-radius:8px;background:#fff;font:inherit;cursor:pointer}
#more:hover{background:#eee}
.sec{margin:14px 14px 0;background:#fff;border:2px solid #1565c0;border-radius:10px;padding:10px 12px}
.sec.un{border-color:#7b1fa2}.sec h2{font-size:16px;margin:0;color:#1565c0}.sec.un h2{color:#7b1fa2}
.sec small{color:#777;display:block;margin-top:2px}.sec .grid{padding:10px 0 4px}
.bd2.lim{background:#1565c0}.bd2.un{background:#7b1fa2}
.shr{font-size:12px;color:#444;margin-top:6px;line-height:1.5}
[hidden]{display:none!important}
</style></head><body>
<header><b id="cnt"></b><small>آخر تحديث __STAMP__</small><label class="mp">الحد الأدنى للخصم <select id="minpct"><option>1</option><option>10</option><option>20</option><option>30</option><option>40</option><option>50</option><option>60</option><option>70</option><option>75</option><option>80</option><option>90</option></select> %</label><button id="unhide" type="button" hidden title="إعادة إظهار العروض المخفية"></button></header>
<section id="inbox" hidden>
<div class="ih"><h2 id="itl"></h2>
<select id="isort"><option value="ev">الأحدث أولاً</option><option value="pct">الأعلى خصماً</option></select>
<button id="markall" type="button">تم الاطلاع على الكل</button></div>
<div class="strip" id="strip"></div>
</section>
<section class="sec" id="sec-sh" hidden><h2>كمية قليلة في المعارض (<span id="sec-sh-n"></span>)</h2>
<small>غير متوفر أونلاين، ويقول الموقع إن في المعرض كمية قليلة (قطعة أو أكثر)</small><div class="grid" id="g-sh"></div></section>
<section class="sec un" id="sec-un" hidden><h2>غير متوفر في أي مكان - اتصل بالمعرض للتأكد (<span id="sec-un-n"></span>)</h2>
<small>الموقع يقول إنه غير متوفر أونلاين ولا في أي معرض، وعليه خصم قوي. قد تبقى قطعة عرض أو علبة مفتوحة، وهذا لا يظهر في الموقع</small><div class="grid" id="g-un"></div></section>
<div class="grid" id="g"></div>
<button id="more" type="button" hidden></button>
<script>
let DATA=__DATA__;const SH=__SH__,UN=__UN__;const STRIP_MAX=100;
const g=document.getElementById('g'),strip=document.getElementById('strip'),inbox=document.getElementById('inbox'),
itl=document.getElementById('itl'),isort=document.getElementById('isort'),markall=document.getElementById('markall'),
cnt=document.getElementById('cnt'),unhide=document.getElementById('unhide');
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const num=x=>+x.toFixed(2);
// ---- permanently hidden offers (kept in the browser; hides every variant of the same product) ----
let HIDDEN={};
try{HIDDEN=JSON.parse(localStorage.getItem('disc_hidden')||'{}')||{}}catch(e){HIDDEN={}}
function saveHidden(){try{localStorage.setItem('disc_hidden',JSON.stringify(HIDDEN))}catch(e){}}
const hkey=o=>o.s+'|'+o.t.trim();
const ALL=DATA;
// ---- minimum discount filter (done here, in the page; remembered by the browser) ----
let MIN=__MINPCT__;try{const m=localStorage.getItem('disc_min');if(m!==null&&m!=='')MIN=+m}catch(e){}
const minsel=document.getElementById('minpct');
if(![...minsel.options].some(op=>+op.value===MIN)){const op=document.createElement('option');op.value=MIN;op.textContent=MIN;minsel.appendChild(op)}
minsel.value=String(MIN);
function applyFilters(){DATA=ALL.filter(o=>!HIDDEN[hkey(o)]&&o.pc>=MIN)}
applyFilters();
minsel.addEventListener('input',()=>{SHOWN=300;MIN=+minsel.value;try{localStorage.setItem('disc_min',MIN)}catch(e){}applyFilters();render();});
const byId={};ALL.forEach(o=>{byId[o.id]=o});
function updateUnhide(){const n=ALL.filter(o=>HIDDEN[hkey(o)]).length;unhide.hidden=n===0;unhide.textContent='المخفية ('+n+') - إعادة إظهار';}
function hideOffer(id){
  const o=byId[id];if(!o)return;
  const k=hkey(o);HIDDEN[k]=new Date().toISOString().slice(0,16);saveHidden();
  DATA=DATA.filter(d=>hkey(d)!==k);
  document.querySelectorAll('.card').forEach(c=>{const d=byId[c.dataset.id];if(d&&hkey(d)===k)c.remove();});
  cnt.textContent='العروض الجديدة — '+DATA.length;
  const total=unreadCount();inbox.hidden=total===0;itl.textContent='جديد ('+total+')';
  updateTitle();updateUnhide();
}
unhide.addEventListener('click',()=>{HIDDEN={};saveHidden();applyFilters();render();});
// ---- read state (kept in the browser, survives the auto refresh) ----
let READ={};
try{READ=JSON.parse(localStorage.getItem('disc_read')||'{}')||{}}catch(e){READ={}}
(function(){const cut=new Date(Date.now()-30*864e5).toISOString().slice(0,16);let ch=false;
 for(const k in READ){if(String(READ[k])<cut){delete READ[k];ch=true}}if(ch)saveRead();})();
function saveRead(){try{localStorage.setItem('disc_read',JSON.stringify(READ))}catch(e){}}
const isUnread=o=>!!o.ev&&READ[o.id]!==o.ev;
const unreadCount=()=>DATA.reduce((n,o)=>n+(isUnread(o)?1:0),0);
function updateTitle(){const n=unreadCount();document.title=(n?'('+n+') ':'')+'العروض الجديدة'}
// ---- cards ----
function card(o){
  const a=document.createElement('a');a.className='card';a.href=o.u;a.target='_blank';a.rel='noopener';a.dataset.id=o.id;
  let b='';if(isUnread(o))b=o.k==='dr'?'<span class="bd2 drop">انخفض السعر</span>':'<span class="bd2 new">جديد</span>';
  const img=o.i?'<img loading="lazy" src="'+esc(o.i)+'" data-o="'+esc(o.o)+'" alt="" '+
   'onerror="if(this.dataset.o&&this.src!==this.dataset.o){this.src=this.dataset.o}else{this.style.visibility=\'hidden\'}">':'';
  a.innerHTML='<div class="im">'+img+'<button class="x" type="button" title="إخفاء نهائي">✕</button><span class="site">'+esc(o.s)+'</span><div class="bds">'+b+'</div></div>'+
   '<div class="bd"><div class="pr"><b>'+num(o.p)+'</b><s>'+num(o.w)+'</s><span class="off">%'+o.pc+' خصم</span></div>'+
   '<div class="br">'+esc(o.b)+'</div><div class="tt">'+esc(o.t)+'</div><div class="tm">'+esc(o.f)+'</div></div>';
  return a;
}
// ---- inbox strip ----
function renderStrip(){
  const total=unreadCount();
  const u=DATA.filter(isUnread);
  u.sort(isort.value==='pct'?(a,b)=>b.pc-a.pc||(a.ev<b.ev?1:-1):(a,b)=>a.ev<b.ev?1:a.ev>b.ev?-1:b.pc-a.pc);
  strip.innerHTML='';
  inbox.hidden=total===0;
  if(!total)return;
  itl.textContent='جديد ('+total+')'+(u.length>STRIP_MAX?' - أحدث '+STRIP_MAX:'');
  const f=document.createDocumentFragment();u.slice(0,STRIP_MAX).forEach(o=>f.appendChild(card(o)));strip.appendChild(f);
}
function markRead(id){
  const o=byId[id];if(!o||!isUnread(o))return;
  READ[id]=o.ev;saveRead();
  document.querySelectorAll('.card[data-id="'+id+'"]').forEach(c=>{
    c.querySelectorAll('.bd2').forEach(b=>b.remove());
    if(strip.contains(c))c.remove();});
  const total=unreadCount();inbox.hidden=total===0;itl.textContent='جديد ('+total+')';updateTitle();
}
['click','auxclick'].forEach(ev=>document.addEventListener(ev,e=>{
  const x=e.target.closest&&e.target.closest('.x');
  if(x){e.preventDefault();e.stopPropagation();if(ev==='click')hideOffer(x.closest('.card').dataset.id);return;}
  const c=e.target.closest&&e.target.closest('.card');if(c)markRead(c.dataset.id);},true));
markall.addEventListener('click',()=>{DATA.forEach(o=>{if(isUnread(o))READ[o.id]=o.ev});saveRead();render();});
isort.addEventListener('input',renderStrip);
// ---- main grid ----
let SHOWN=300;const more=document.getElementById('more');
more.addEventListener('click',()=>{SHOWN+=300;render();});
function render(){
  cnt.textContent='العروض — '+DATA.length+(DATA.length>SHOWN?' (المعروض '+SHOWN+')':'');
  g.innerHTML='';
  const f=document.createDocumentFragment();DATA.slice(0,SHOWN).forEach(o=>f.appendChild(card(o)));g.appendChild(f);
  more.hidden=DATA.length<=SHOWN;more.textContent='عرض المزيد ('+(DATA.length-SHOWN)+')';
  renderStrip();updateTitle();updateUnhide();renderExtra();
}
function card2(o,cls,label){
  const a=document.createElement('a');a.className='card';a.href=o.u;a.target='_blank';a.rel='noopener';
  const im=document.createElement('div');im.className='im';
  if(o.i){const img=document.createElement('img');img.loading='lazy';img.src=o.i;img.alt='';img.onerror=()=>{img.style.visibility='hidden'};im.appendChild(img);}
  const bds=document.createElement('div');bds.className='bds';
  bds.innerHTML='<span class="bd2 '+cls+'">'+label+(o.nw?' · جديد':'')+'</span>';im.appendChild(bds);
  const bd=document.createElement('div');bd.className='bd';
  bd.innerHTML='<div class="pr"><b>'+num(o.p)+'</b><s>'+num(o.w)+'</s><span class="off">%'+o.pc+' خصم</span></div>'+
   '<div class="tt">'+esc(o.t)+'</div>'+(o.sh?'<div class="shr">'+esc(o.sh)+'</div>':'')+'<div class="tm">'+esc(o.f)+'</div>';
  a.appendChild(im);a.appendChild(bd);return a;
}
function renderExtra(){
  [['sec-sh','g-sh',SH,'lim','كمية قليلة'],['sec-un','g-un',UN,'un','غير متوفر']].forEach(function(c){
    const sec=document.getElementById(c[0]),gr=document.getElementById(c[1]),arr=c[2];
    sec.hidden=!arr.length;gr.innerHTML='';document.getElementById(c[0]+'-n').textContent=arr.length;
    const f=document.createDocumentFragment();arr.forEach(o=>f.appendChild(card2(o,c[3],c[4])));gr.appendChild(f);
  });
}
render();
</script></body></html>"""


def _pack_extra(lst):
    cutoff = (datetime.datetime.now() - datetime.timedelta(hours=HISTORY_HOURS)).isoformat(timespec="minutes")
    data = [{"id": o["id"], "t": o["title"], "p": o["price"], "w": o["was"], "pc": o["pct"], "u": o["url"],
             "i": small_img(o.get("img", "")), "f": (o.get("found") or "")[11:16], "sh": o.get("sh", ""),
             "nw": bool(o.get("new_at")) and o["new_at"] >= cutoff} for o in lst]
    return json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")


def build_page(items, sh=(), un=()):
    items = sorted(unique(items), key=lambda o: (-o["pct"], o["site"]))
    data = []
    for o in items:
        found = o.get("found", "")
        data.append({
            "id": o["id"], "s": o["site"], "t": o["title"], "b": o.get("brand", ""),
            "p": o["price"], "w": o["was"], "pc": o["pct"], "u": o["url"],
            "i": small_img(o.get("img", "")), "o": o.get("img", ""),
            "f": found[11:16],
            # entries saved by the older version have no "kind": not shown as unread
            "ev": found if o.get("kind") else "",
            "k": o.get("kind", ""),
        })
    blob = json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    return (PAGE_TEMPLATE.replace("__REFRESH__", str(PAGE_REFRESH_SEC))
            .replace("__STAMP__", now).replace("__MINPCT__", str(MIN_DISCOUNT_PCT))
            .replace("__SH__", _pack_extra(sh)).replace("__UN__", _pack_extra(un))
            .replace("__DATA__", blob))


def update_results(events, now_dt, current=()):
    """events = new offers (kind 'nw') and price drops (kind 'dr'); current = every offer found by this
    scan (shown on the page too, not flagged as new). Keeps offers found in the last HISTORY_HOURS
    and rewrites the results page, which has its own minimum-discount filter."""
    hist = load_history()
    cutoff = (now_dt - datetime.timedelta(hours=HISTORY_HOURS)).isoformat(timespec="minutes")
    stamp = now_dt.isoformat(timespec="minutes")
    for o in events:
        o["found"] = stamp
    ids = {o["id"] for o in events}
    kept = [h for h in hist if h["id"] not in ids and h.get("found", "") >= cutoff
            and h["pct"] >= COLLECT_MIN_PCT and not is_excluded(h["title"])]
    have = ids | {h["id"] for h in kept}
    snapshot = [dict(o, found=stamp) for o in current if o["id"] not in have]
    hist = unique(sorted(kept + events + snapshot, key=lambda o: o.get("found", ""), reverse=True))
    HISTORY_FILE.write_text(json.dumps(hist, ensure_ascii=False), encoding="utf-8")
    ex = load_extra()
    HTML_FILE.write_text(build_page(hist, ex["sh"], ex["un"]), encoding="utf-8")
    return hist


# ----------------------------- Notifications / browser --------------
def _ntfy(title, message):
    body = json.dumps({"topic": NTFY_TOPIC, "title": title, "message": message[:1000]}).encode()
    req = urllib.request.Request("https://ntfy.sh/", data=body, headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=20):
        pass


def notify(title: str, message: str):
    if NTFY_TOPIC:
        try:
            _ntfy(title, message)
        except Exception as e:
            print(f"[NTFY FAILED] {e}")
        print(f"[NOTIFY] {title}: {message}")
        return
    try:
        from winotify import Notification
        Notification(app_id="Discount Monitor", title=title, msg=message[:250]).show()
        return
    except Exception:
        pass
    try:
        from plyer import notification
        notification.notify(title=title, message=message[:250], timeout=10)
        return
    except Exception:
        pass
    print(f"[NOTIFY] {title}: {message}")


def open_urls(urls):
    if not urls:
        return
    if BROWSER == "firefox":
        exe = next((p for p in FIREFOX_PATHS if Path(p).exists()), None)
        if exe:
            subprocess.Popen([exe, "-new-tab", *urls])   # all in one Firefox window
            return
        print("Firefox not found, using the default browser")
    for u in urls:
        webbrowser.open_new_tab(u)


# ----------------------------- State --------------------------------
def load_state():
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    return {}


def save_state(state):
    STATE_FILE.write_text(json.dumps(state, ensure_ascii=False), encoding="utf-8")


# ----------------------------- Scan ---------------------------------
def installed_chrome_major():
    """Major version of the Chrome that is installed on this PC (e.g. 156), or None if unknown."""
    def major_of(text):
        m = re.search(r"(\d+)\.\d+\.\d+\.\d+", text or "")
        return int(m.group(1)) if m else None

    if sys.platform == "win32":
        try:
            import winreg
            for hive, key in ((winreg.HKEY_CURRENT_USER, r"Software\Google\Chrome\BLBeacon"),
                              (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Google\Chrome\BLBeacon"),
                              (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Google\Chrome\BLBeacon")):
                try:
                    with winreg.OpenKey(hive, key) as k:
                        v = major_of(winreg.QueryValueEx(k, "version")[0])
                        if v:
                            return v
                except OSError:
                    pass
        except ImportError:
            pass
        for base in (os.environ.get("PROGRAMFILES"), os.environ.get("PROGRAMFILES(X86)"),
                     os.environ.get("LOCALAPPDATA")):
            if not base:
                continue
            exe = Path(base) / "Google" / "Chrome" / "Application" / "chrome.exe"
            if exe.exists():
                try:
                    out = subprocess.run(
                        ["powershell", "-NoProfile", "-Command",
                         f"(Get-Item '{exe}').VersionInfo.ProductVersion"],
                        capture_output=True, text=True, timeout=15).stdout
                    v = major_of(out)
                    if v:
                        return v
                except Exception:
                    pass
    else:
        for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
            exe = shutil.which(name)
            if exe:
                try:
                    v = major_of(subprocess.run([exe, "--version"], capture_output=True,
                                                text=True, timeout=15).stdout)
                    if v:
                        return v
                except Exception:
                    pass
    return None


_CHROME_MAJOR = None    # remembered once a driver has started successfully


def _build_options():
    opts = uc.ChromeOptions()
    opts.add_argument("--lang=ar-SA")
    # Don't load images while scanning (Firefox, used for viewing offers, loads them normally)
    opts.add_argument("--blink-settings=imagesEnabled=false")
    opts.add_argument("--disable-notifications")      # no "allow notifications?" pop-up from the site
    opts.add_experimental_option("prefs", {"profile.managed_default_content_settings.images": 2,
                                           "profile.default_content_setting_values.notifications": 2})
    # Return as soon as the HTML is parsed (the product data is inside it); don't wait for trackers/ads
    opts.page_load_strategy = "eager"
    return opts


def make_driver():
    """Start Chrome with a chromedriver that matches the installed Chrome version.
    Chrome updates itself, so the version is detected on every start; if it is still
    reported as a mismatch, the real version is read from the error and the start is retried."""
    global _CHROME_MAJOR
    major = installed_chrome_major() or _CHROME_MAJOR
    d = None
    for _attempt in range(3):
        try:
            kw = {"version_main": major} if major else {}
            kw["user_data_dir"] = str(HERE / "jarir_chrome_profile")    # keeps cookies between runs
            d = uc.Chrome(options=_build_options(), **kw)    # new options object on every try
            break
        except Exception as e:
            m = re.search(r"Current browser version is (\d+)", str(e))
            if m and int(m.group(1)) != major:
                major = int(m.group(1))
                print(f"    Chrome version mismatch; retrying with chromedriver {major}")
                continue
            raise
    if d is None:
        raise RuntimeError("could not start Chrome")
    _CHROME_MAJOR = major
    d.set_page_load_timeout(PAGE_TIMEOUT_SEC)
    try:    # shorter wait on a stuck chromedriver connection (default is 120s)
        d.command_executor._client_config.timeout = PAGE_TIMEOUT_SEC + 30
    except Exception:
        try:
            import warnings
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                d.command_executor.set_timeout(PAGE_TIMEOUT_SEC + 30)
        except Exception:
            pass
    return d


class Browser:
    """Chrome wrapper that survives timeouts: stops slow pages, restarts a hung browser."""

    def __init__(self):
        self.d = None

    def start(self):
        self.stop()
        self.d = make_driver()

    def stop(self):
        if self.d is not None:
            try:
                self.d.quit()
            except Exception:
                pass
            self.d = None

    def source(self, url, ready=None, stop=True):
        """Load url and return the page HTML. If `ready(html)` is given, wait until it is true
        (up to READY_WAIT_SEC) so a half-loaded page is never parsed."""
        for attempt in range(2):
            try:
                if self.d is None:
                    self.start()
                try:
                    self.d.get(url)
                except TimeoutException:
                    pass                      # keep waiting below for the data to finish arriving
                deadline = time.time() + READY_WAIT_SEC
                while True:
                    src = self.d.page_source
                    if ready is None or ready(src) or time.time() > deadline:
                        break
                    time.sleep(1)
                if stop:
                    try:
                        self.d.execute_script("window.stop()")
                    except Exception:
                        pass
                time.sleep(random.uniform(1, 2))
                return src
            except Exception as e:
                print(f"    fetch failed ({type(e).__name__}); restarting Chrome")
                try:
                    self.start()
                except Exception as e2:
                    print(f"    could not restart Chrome: {e2}")
                    self.d = None
        return None


_JARIR_QC_JS = r"""
const app = document.querySelector('#__nuxt') && document.querySelector('#__nuxt').__vue_app__;
if (!app) return null;
const prov = app._context.provides;
let qc = null;
for (const k of Reflect.ownKeys(prov)) {
  const v = prov[k];
  if (v && typeof v.getQueryCache === 'function') { qc = v; break; }
}
if (!qc) return null;
const hits = [];
for (const q of qc.getQueryCache().getAll()) {
  if (q.queryKey && q.queryKey[0] === 'category-products') {
    const pages = (q.state.data && q.state.data.pages) || [];
    for (const p of pages) {
      const hs = (p.data && p.data.hits && p.data.hits.hits) || [];
      for (const h of hs) hits.push(h._source);
    }
  }
}
"""

# how many products the open page has loaded so far (cheap, used while waiting)
_JARIR_COUNT_JS = _JARIR_QC_JS + "return hits.length;"

# only the products from index arguments[0] on, with just the fields the script needs
_JARIR_SLICE_JS = _JARIR_QC_JS + r"""
const keys = ['sku', 'id', 'name', 'meta_title', 'url_path', 'url_key', 'final_price', 'special_price',
              'regular_price', 'price', 'brand', 'image', 'small_image', 'is_stock_available'];
return JSON.stringify(hits.slice(arguments[0]).map(x => { const o = {}; for (const k of keys) o[k] = x[k]; return o; }));
"""

_JARIR_SCROLL_JS = r"""
const h = document.documentElement.scrollHeight;
window.scrollTo(0, Math.max(0, h - 1500));
const t = document.querySelector('.infinite-scroll-trigger');
if (t) t.scrollIntoView({block: 'center'});
window.scrollTo(0, document.documentElement.scrollHeight);
"""

_JARIR_CLOSE_LANG_JS = r"""
// best effort: close the "choose country / language" pop-up by choosing Saudi Arabia - Arabic
const els = Array.from(document.querySelectorAll('button, a, div, li'));
const hit = els.filter(e => /^\s*السعودية\s+عربي\s*$/.test(e.innerText || '')).pop();
if (hit) { hit.click(); return true; }
return false;
"""

_JARIR_CHALLENGE_JS = r"""
if (document.querySelector('#px-captcha, [id*="px-captcha"], iframe[src*="captcha"]')) return true;
const t = document.body ? document.body.innerText : '';
return /(لست\s+(برنامج\s+)?(آلي|روبوت)|اضغط\s+باستمرار|استمر\s+بالضغط|not a robot|press\s*&\s*hold|verify you are human)/i.test(t);
"""


def jarir_live_count(d):
    """Number of products the open Jarir page has loaded so far (None if the page is not ready)."""
    try:
        n = d.execute_script(_JARIR_COUNT_JS)
        return int(n) if n is not None else None
    except Exception:
        return None


def jarir_live_slice(d, start):
    """Products loaded in the open page from index `start` on (None if the page is not ready)."""
    try:
        raw = d.execute_script(_JARIR_SLICE_JS, start)
        return json.loads(raw) if raw is not None else None
    except Exception:
        return None


def _jarir_challenge(d):
    """True while Jarir shows its 'press and hold to confirm you are human' box."""
    try:
        return bool(d.execute_script(_JARIR_CHALLENGE_JS))
    except Exception:
        return False


def wait_for_human(d, max_min=10):
    """The check must be done by a person (press and hold the button): notify and wait in the Chrome window."""
    notify("Jarir monitor", "Jarir asks you to confirm you are human - press and hold the button in the Chrome window.")
    print(f"  Jarir: human check shown - do it in the Chrome window (waiting up to {max_min} min)")
    t_end = time.time() + max_min * 60
    while time.time() < t_end:
        time.sleep(5)
        if not _jarir_challenge(d):
            print("  Jarir: check passed")
            time.sleep(3)
            return True
    print("  Jarir: the check was not done in time")
    return False


def _jarir_fail_info(d):
    """Short description of what the browser got instead of the products (for the log)."""
    try:
        info = d.execute_script("""
            const n = performance.getEntriesByType('navigation')[0];
            return JSON.stringify({status: n ? n.responseStatus : null,
                                   text: (document.body ? document.body.innerText : '').slice(0, 160)});
        """)
        return info
    except Exception as e:
        return f"<{type(e).__name__}>"


def scan_jarir(browser, site):
    """Page 1 comes from the URL (parsed from the page source); the following pages are loaded by
    scrolling to the bottom (infinite scroll) and read from the page's own data cache."""
    res = None
    # Warm-up: a brand-new browser session often gets CF_5xx on its very first request, so visit the
    # home page first (result ignored). Retries alternate between two equivalent URLs.
    try:
        browser.source(site["base"] + "/", stop=False)
        time.sleep(random.uniform(4, 7))
    except Exception:
        pass
    urls = [site["url"], site.get("url_alt") or site["url"]]
    for attempt in range(4):
        url = urls[attempt % 2]
        src = browser.source(url, ready=lambda t: page_has_data(t, site), stop=False)
        if _jarir_challenge(browser.d) and wait_for_human(browser.d):
            src = browser.d.page_source
        res = parse(site, src) if src else None
        if res is not None and res[1] > 0:
            break
        print(f"  {site['name']}: attempt {attempt + 1} failed -> {_jarir_fail_info(browser.d)}")
        time.sleep(10 * (attempt + 1))
    if res is None or res[1] == 0:
        print(f"  {site['name']}: no products found (server error CF_5xx, blocked, or layout differs)")
        return None
    offers = {o["id"]: o for o in res[0]}
    d = browser.d
    try:
        # wait until the page is alive (hydrated) so scrolling can load more
        t_end = time.time() + 30
        sources = None
        while time.time() < t_end:
            sources = jarir_live_slice(d, 0)
            if sources:
                break
            time.sleep(1)
        if not sources:
            print(f"  {site['name']}: page data not readable from the live page - only the first page was read")
        else:
            try:
                d.execute_script(_JARIR_CLOSE_LANG_JS)
            except Exception:
                pass
            loads, stalls = 0, 0
            while loads < JARIR_MAX_PAGES and stalls < 3:
                before = len(sources)
                d.execute_script(_JARIR_SCROLL_JS)
                grew = False
                t_end = time.time() + 25                 # up to 25 s for the next page to arrive
                while time.time() < t_end:
                    time.sleep(0.7)
                    n = jarir_live_count(d)
                    if n is not None and n > before:
                        more = jarir_live_slice(d, before)
                        if more:
                            sources += more
                            grew = True
                            break
                if not grew:
                    if _jarir_challenge(d):
                        if wait_for_human(d):
                            continue                      # done: load the next page again
                        break
                    stalls += 1                           # 3 times in a row = end of the list
                    continue
                stalls = 0
                loads += 1
                if loads % 25 == 0:
                    print(f"  {site['name']}: {len(sources)} products loaded so far...")
                time.sleep(random.uniform(0.8, 2.0))
            offers = {o["id"]: o for o in _jarir_offers(site, sources)}
            print(f"  {site['name']}: loaded {len(sources)} products by scrolling")
    except Exception as e:
        print(f"  {site['name']}: scrolling failed ({type(e).__name__}); using what was loaded so far")
        try:
            if sources:
                offers = {o["id"]: o for o in _jarir_offers(site, sources)}
        except Exception:
            pass
    print(f"  {site['name']}: {len(offers)} discounted offers after exclusions")
    return offers or None


class ApiRefused(Exception):
    def __init__(self, msg, status=None):
        super().__init__(msg)
        self.status = status


JARIR_API_BASE = "https://www.jarir.com/api/catalogv2/product/store/sa-ar"
JARIR_API_WINDOW = 10000        # the API cannot be paged past from+size = 10,000: bigger categories are split
JARIR_CATEGORY_NAMES = {"4": "school supplies", "5": "toys", "11": "computer supplies", "1651": "digital cards",
                        "10001": "computers", "10002": "mobiles & electronics", "10003": "smart TV accessories",
                        "10004": "musical instruments", "10005": "video games", "10006": "books",
                        "10007": "office supplies", "10008": "arts & crafts"}
# category code -> codes of its sub-categories (taken from Jarir's own category tree)
JARIR_CATEGORY_TREE = json.loads('{"4":["24","38","50","61","67","83","96","1506","99","113","122","135","141","148"],"5":["23","37","44","62","73","81","87","106","109","125","136","5130"],"11":["21","42","49","56","68","82","93","107","118","127","129","147","158","165","176","177","185","192","1252"],"21":["232","236","238","239","240"],"23":["334","493","513","618","728","830","1860","1866","1867","1868","1869","1870","1903"],"24":["388","470","608","720","787","835"],"37":["370","644","1612","1861","1862","1865","1904"],"38":["361","569","727","1891","1909"],"42":["241","243","246","248","250","251","252"],"50":["357","518","583"],"56":["287","439","616"],"61":["355"],"62":["378","526","1873","1874","1875","1876"],"67":["307","541"],"81":["5123"],"82":["253","1666","1667","1668","1669","1670"],"83":["369","477"],"87":["501","599","737","1850","1851","1852","1853","1854","1855","1856","1857","1858","1859","1901","1902"],"93":["323","479","609","742","794","848","901","911","1505"],"99":["286"],"107":["330"],"113":["377","444","1887","1888","1889","1890","1905","1906","1907","1908"],"118":["383","509","561","743","792","846"],"125":["345","1863","1864","1871","1872"],"127":["329","488","643"],"129":["321","443","617","685","780"],"135":["390","504"],"136":["552","567","1877","1878","1879","1880","1881","1882","1883","1884","1911","1912","6000","6001"],"141":["269","422","566","677","758","822"],"147":["332","503","581"],"148":["336","553"],"165":["288","421","662","796","843","871"],"176":["391","554"],"177":["350","507","631"],"501":["6013","6014"],"1651":["1652","1653","1654","1655","1656","1657","1659","1660","1734","1735","1736","1780"],"1860":["6011"],"1878":["6009","6010"],"1880":["6006","6007","6008"],"1883":["6002","6005"],"5130":["6015","6016","6017"],"6002":["6003","6004"],"10001":["21001","21002","21003","21004","21005","21006","21007"],"10002":["21008","21009","21010","21011","21012","21013"],"10003":["21038","21064","21065","21066","21037","21052","21053","21015","21016","21014"],"10004":["21017","21061"],"10005":["21054","21055","21024","21025","21031","21028","21029","21033","21036","21063","21062"],"10006":["21059","21050","21060","21051"],"10007":["21056","21057","21058","21068"],"10008":["21069","21070","21071"],"21001":["30092","30001","30247","30124","30002","30003","30004","30005","30006"],"21002":["30093","30248","30007","30125","30008","30009"],"21003":["30094","30010","30249","30126","30011","30012","30013","30014"],"21004":["30095","30015","30250","30127","30016","30017"],"21005":["30096","30018","30128","30019","30020"],"21006":["30097","30021","30251","30129","30022","30023"],"21007":["30130","30024","30025","30026","30027","30028","30029","30030","30091"],"21008":["30098","30252","30118","30031"],"21009":["30099","30253","30119","30032","30033","30034","30035","30036","30037","30038","30090"],"21010":["30100","30039","30040","30120","30041","30051"],"21011":["30101","30121","30042","30043","30044"],"21012":["30102","30045","30122","30046","30050"],"21013":["30123","30047","30048","30269","30052"],"21015":["30275","30146","30147","30148","30149","30150","30151"],"21016":["30137","30138","30139","30140"],"21017":["30075","30076","30078","30077","30079","30080","30081"],"21024":["30082","30083","30084","30162"],"21025":["30085","30086"],"21028":["30053","30054","30055","30057"],"21029":["30058","30059","30060","30061"],"21031":["30062","30063","30064","30276","30065","30066","30068","30069","30070"],"21033":["30071","30072","30073","30074"],"21036":["30087","30088","30089"],"21037":["30142","30143","30144","30141"],"21038":["30131","30132","30133","30202","30135","30134","30136"],"21050":["30197","30254","30198","30201","30103","30104","30105","30106","30107","30108","30215"],"21051":["30219","30255","30220","30109","30110","30111","30112","30113","30114","30237","30236","30223","30216"],"21052":["30211","30212","30213","30214"],"21053":["30115","30116","30117","30272"],"21054":["30152","30153","30154","30155","30156","30157","30158"],"21055":["30159","30160","30161","30273"],"21056":["30307","30277","30163","30164","30165","30166","30167","30168","30169","30170","30171","30172"],"21057":["30308","30278","30173","30174","30175","30176"],"21058":["30309","30279","30177","30258","30178","30179","30281"],"21059":["30229","30256","30230","30233","30187","30188","30189","30190","30191","30192","30218"],"21060":["30224","30257","30225","30181","30182","30183","30184","30185","30186","30235","30234","30228","30217"],"21063":["30238","30239","30240","30241","30242","30243","30244","30245","30246"],"21064":["30193","30194","30195","30196"],"21065":["30203","30204","30205","30206"],"21066":["30207","30208","30209","30210"],"21068":["30310","30274","30263","30264","30265","30271","30268","30266","30267","30270"],"21069":["30311","30314","30282","30283","30284","30285","30286","30287"],"21070":["30312","30315","30288","30289","30290","30291","30292","30293","30294","30295","30296","30297","30298","30299","30300"],"21071":["30313","30316","30301","30302","30303","30304","30305","30306"],"30001":["40001","40002","40003","40004","40005","40006"],"30002":["40007","40008","40009","40010","40011","40012"],"30003":["40013","40014","40015","40016","40017","40018"],"30004":["40019","40020","40021","40022"],"30005":["40023","40024","40025","40026","40027"],"30007":["40028","40029","40030"],"30008":["40031","40032","40033","40034","40035","40036"],"30010":["40037","40038","40039","40040","40784","40041"],"30011":["40042","40043","40044","40045"],"30012":["40046","40047","40048","40049","40050","40051","40052"],"30013":["40053","40054","40055","40056","40057","40058"],"30015":["40059","40060","40061","40062","40063","40064"],"30016":["40065","40066","40067","40068","40069","40070"],"30018":["40071","40072","40073","40074"],"30019":["40075","40076","40077","40078","40079"],"30021":["40080","40081","40082","40083"],"30022":["40084","40085","40086","40087","40088"],"30024":["40089","40090","40091","40092","40093","40094","40095"],"30025":["40096","40097","40098","40099","40100","40101"],"30026":["40102","40103","40104","40105","40106","40107"],"30027":["40108","40109","40110","40111","40112","40113"],"30028":["40114","40115","40116","40117","40118","40119"],"30029":["40120","40121","40122","40123","40124"],"30030":["40125","40126","40127","40128","40129","40130"],"30032":["40131","40132","40133","40134","40135","40136"],"30033":["40137","40138","40139","40140","40141"],"30034":["40142","40143","40144","40145","40146"],"30035":["40147","40148","40149","40150"],"30036":["40151","40152","40153","40154"],"30037":["40155","40156","40157","40158"],"30038":["40159","40160","40161","40162","40163","40164"],"30039":["40165","40166","40167","40168","40169"],"30040":["40170","40171","40172","40173","40174","40175"],"30041":["40176","40177","40178","40179","40180","40844"],"30042":["40182","40183","40184"],"30043":["40185","40186","40187","40188"],"30045":["40189","40190","30056","40191","40192","40846"],"30046":["40193","40194","40195","40196","40197","40198","40199"],"30047":["40200","40201","40202","40203","40204"],"30048":["40205","40206","40207","40209","40698","40845"],"30087":["40210","40211"],"30088":["40213","40214"],"30092":["40215","40216","40217","40218","40219","40220","40221","40222","40223","40224"],"30093":["40225","40226","40227","40228","40229","40230","40231","40232","40233","40234","40235"],"30094":["40236","40237","40238","40239","40240","40241","40242","40243"],"30095":["40244","40245","40246","40247","40248"],"30096":["40249","40250","40251","40252","40253","40254","40255","40256","40257","40258","40259"],"30097":["40263","40264","40265","40266","40267","40268","40269","40270","40271"],"30098":["40272","40273","40274","40275","40276","40277","40278","40279","40280","40281","40282","40283","40284"],"30099":["40285","40286","40287","40288","40289","40290","40291","40292","40293","40294","40295"],"30100":["40296","40297","40298","40299","40300","40301","40302","40303","40304","40305","40306"],"30101":["40307","40308","40309","40310","40311","40312","40313","40314","40847","40848"],"30102":["40318","40319","40320","40321","40322","40323","40324","40325"],"30103":["40332","40333"],"30104":["40334","40335","40336","40337","40338"],"30105":["40339","40340"],"30106":["40342","40343","40341","40782"],"30107":["40344","40345","40346","40347","40348","40349","40350"],"30108":["40351","40352","40353","40354","40355","40356","40357"],"30109":["40358","40359","40360","40361","40362","40363","40364","40365","40366","40367"],"30110":["40368","40369","40370","40371","40372","40373"],"30111":["40374","40375","40376","40377","40378","40379"],"30112":["40380","40381","40382","40383"],"30113":["40384","40385","40386","40387"],"30114":["40388","40389","40390"],"30118":["40391","40392","40393","40394","40395"],"30119":["40396","40397","40398","40399","40831","40838"],"30120":["40400","40401","40402","40403","40832","40839"],"30121":["40404","40405","40406","40407","40688"],"30122":["40408","40409","40410","40411"],"30123":["40412","40413","40414","40415"],"30124":["40416","40417","40418","40419","40420"],"30125":["40421","40422","40423","40424","40634"],"30126":["40425","40426","40427","40428","40830"],"30127":["40429","40430","40431","40432"],"30128":["40433","40434","40435","40436","40829"],"30129":["40437","40438","40439","40440"],"30130":["40441","40442","40444","40443","40837"],"30162":["40445","40446","40447","40448","40449","40450","40451"],"30163":["40452","40453","40454","40455","40456","40457","40458","40459"],"30164":["40460","40461","40462","40463","40464","40465","40466"],"30165":["40467","40470","40471","40707","40708"],"30166":["40475","40474","40476","40477"],"30167":["40478","40479","40480","40481","40709"],"30168":["40482","40483","40484","40485"],"30169":["40486","40487","40488","40489"],"30170":["40490","40491","40493","40494","40495","40496"],"30171":["40497","40498","40499","40500","40501","40781","40785","40502","40503"],"30172":["40504","40505","40506","40507","40508"],"30173":["40509","40510","40511","40512","40513","40514","40515"],"30174":["40516","40517","40518","40519","40520"],"30175":["40522","40523","40524","40525","40526","40527"],"30176":["40528","40711","40529","40530"],"30177":["40531","40532","40533","40534","40535","40536"],"30178":["40537","40538","40539","40540","40720","40721","40722","40866"],"30179":["40541","40542","40543","40544","40545","40546"],"30181":["40550","40551","40552","40553","40554","40555","40556","40557","40558","40559"],"30182":["40560","40561","40562","40563","40564","40565"],"30183":["40566","40567","40568","40569","40570","40571"],"30184":["40573","40572","40574","40575"],"30185":["40576","40577","40578","40579"],"30186":["40580","40581","40582"],"30187":["40583","40584"],"30188":["40635","40636","40637","40638","40639"],"30189":["40640","40641"],"30190":["40642","40643","40644","40783"],"30191":["40595","40596","40597","40598","40599","40600","40601","40609"],"30192":["40645","40646","40647","40648","40649","40650"],"30197":["40667","40668","40669","40670","40675","40676"],"30219":["40659","40660","40697","40662"],"30223":["40679","40651","40652","40653"],"30224":["40663","40664","40665","40666"],"30228":["40680","40655","40656","40657"],"30229":["40671","40672","40673","40674","40677","40678"],"30247":["40610","40611","40612","40613"],"30248":["40614","40615","40616","40617"],"30249":["40618","40619","40620","40621"],"30250":["40622","40623","40624","40625"],"30251":["40626","40627","40628","40629"],"30252":["40858","40630","40631","40632","40633"],"30253":["40868","40869","40681","40682","40683","40684","40685","40686","40687"],"30254":["40689","40690","40691","40692","40833"],"30255":["40693","40694","40695","40696","40835"],"30256":["40699","40700","40701","40702","40834"],"30257":["40703","40704","40705","40706","40836"],"30258":["40712","40713","40714","40715","40716","40717","40718","40719","40867","41012"],"30263":["40745","40746","40747","40748","40749","40750","40751","40752","40753","40823","40828"],"30264":["40754","40755","40789","40790","40791","40792","40786","40788","40787"],"30265":["40756","40757","40793","40794","40795","40826","40825","40824"],"30266":["40758","40759","40760","40761","40762","40763","40764","40765","40805","40806","40807","40808","40809","40810","40811","40812"],"30267":["40766","40767","40796","40797","40798"],"30268":["40768","40769","40770","40771","40772","40773","40774","40775","40776","40777","40778","40780","40821","40822","40819","40820","40849"],"30270":["40799","40800","40801","40802","40803","40804"],"30271":["40813","40814","40815","40816","40817","40818","40827"],"30274":["40840","40841","40842","40843"],"30277":["40850","40857","40871","40988"],"30278":["40851","40852","40872","40989"],"30279":["40853","40854","40873","40990"],"30281":["40859","40860","40861","40862","40863","40864","40865"],"30282":["40921","40922","40923","40924"],"30283":["40925","40926"],"30284":["40927","40928"],"30285":["40929","40930","40931","40932","40933"],"30286":["40934","40935","40936","40937"],"30287":["40938","40939","40940","40941"],"30288":["40874","40875","40876"],"30289":["40877","40878","40879","40880","40881","40882","40987"],"30290":["40883","40884","40885","40886"],"30291":["40887","40888","40889","40890"],"30292":["40891","40892","40893","40894"],"30293":["40895","40896"],"30294":["40897","40898"],"30295":["40899","40900","40901"],"30296":["40902","40903","40904"],"30297":["40905","40906","40907","40908"],"30298":["40911","40909","40910"],"30299":["40912","40913","40914","40915","40916"],"30300":["40917","40918","40919","40920"],"30301":["40942","40943"],"30302":["40944","40945","40946"],"30303":["40947","40948"],"30304":["40949","40950","40951","40952"],"30305":["40953","40954"],"30306":["40955"],"30307":["40956","40957","40958","40959","40960","40961","40962","40963","40964","40965","40966"],"30308":["40967","40968","40969"],"30309":["40970","40971","40972","40973","40975","40974","40976","40977","40978"],"30310":["40979","40980","40981","40982","40983","40984","40985","40986"],"30311":["40991","40992","40993","40994","40995","40996","40997","40998","40999","41000"],"30312":["41001","41002","41003","41004","41005","41006","41007","41008","41009","41010"],"30313":["41011","41013","41014","41015","41016","41017","41018","41019","41020","41021"],"30314":["41022","41023","41024"],"30315":["41025","41026","41027"],"30316":["41028","41029","41030"],"40332":["50001","50002","50003","50004","50005","50006","50007","50008","50009","50010"],"40333":["50011","50012"],"40334":["50013","50014","50015"],"40336":["50017","50018","50019"],"40338":["50021","50022"],"40339":["50023","50024","50025","50026","50027","50028","50029"],"40340":["50030","50031","50032","50033","50034","50035","50036"],"40342":["50038","50039","50040"],"40351":["50049","50050","50051","50052","50053"],"40352":["50054","50055","50056","50057"],"40353":["50058","50059","50060"],"40354":["50061","50062"],"40355":["50063","50064","50065","50066","50067","50068","50069"],"40356":["50070","50071","50072","50073","50074","50075","50076"],"40357":["50077","50078","50079","50080","50081","50082","50083","50084","50085","50086","50087","50088","50089","50090","50091","50092","50093","50094","50096","50097","50098","50099","50100","50101","50102","50103","50104","50198","50203","50204"],"40583":["50105","50106","50107","50108","50109","50110","50111","50112","50113","50114"],"40584":["50115","50116","50205"],"40635":["50144","50145","50146","50147","50148","50149","50150","50151"],"40637":["50153","50154","50155"],"40638":["50156","50157","50158","50159"],"40639":["50160","50161"],"40640":["50162","50163","50164","50165","50166"],"40641":["50167","50168","50169","50170","50171","50172"],"40642":["50173","50174","50176","50177","50178"],"40644":["50181","50182","50183","50184","50185"],"40645":["50142","50143"],"40646":["50135","50137","50138"],"40647":["50132","50133","50134"],"40648":["50128","50129","50130","50131"],"40649":["50120","50122","50123","50124","50125","50126","50127"],"40650":["50117","50118","50119"],"40782":["50194","50201","50202","50195"],"40783":["50196","50199","50200","50197"]}')
_API_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
                  "Chrome/130.0.0.0 Safari/537.36",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "ar-SA,ar;q=0.9",
}


JARIR_API_RETRIES = 4           # network errors (timeout / SSL / DNS) are retried before giving up


def _jarir_api_page(code, start, size):
    """One request of Jarir's product list API -> (hits, total). Raises ApiRefused on any problem."""
    url = f"{JARIR_API_BASE}/category_codes/{code}/size/{size}/from/{start}/sort-priority/asc"
    body = None
    for attempt in range(JARIR_API_RETRIES):
        last = attempt == JARIR_API_RETRIES - 1
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=_API_HEADERS), timeout=60) as r:
                body = r.read().decode("utf-8", "replace")
            break
        except urllib.error.HTTPError as e:
            if e.code in (502, 503, 504) and not last:      # temporary server trouble
                time.sleep(5 * (attempt + 1))
                continue
            raise ApiRefused(f"HTTP {e.code} for category {code} from={start} size={size}", e.code)
        except Exception as e:                              # timeout, SSL handshake, DNS...
            if not last:
                time.sleep(5 * (3 ** attempt))              # 5s, 15s, 45s
                continue
            raise ApiRefused(f"{type(e).__name__}: {e}")
    try:
        data = json.loads(body)["data"]["hits"]
        hits = data["hits"]
        total = data["total"]
        total = total.get("value") if isinstance(total, dict) else total
        return hits, int(total)
    except (ValueError, KeyError, TypeError):
        raise ApiRefused("unexpected answer: " + body[:120].replace("\n", " "))


def _read_kids(site, code, st, depth):
    kids = JARIR_CATEGORY_TREE.get(code, [])
    for kid in kids:
        try:
            _api_collect(site, kid, st, depth + 1)
        except ApiRefused as e:
            if e.status in (403, 429):
                raise
            print(f"  {site['name']}: sub-category {kid}: {e}")
    return bool(kids)


def _api_collect(site, code, st, depth=0):
    """Read one category. If it is too big for the API window, or the API stops early / the network drops
    in the middle, the rest is read through its sub-categories (duplicates are removed by product id)."""
    start = 0
    while True:
        size = max(1, min(st["size"], JARIR_API_WINDOW - start))
        try:
            hits, total = _jarir_api_page(code, start, size)
        except ApiRefused as e:
            if start == 0 and st["size"] != 12 and e.status in (400, 404, 422, 500):
                st["size"] = 12                    # maybe the bigger page size is not accepted
                continue
            if start > 0 and (e.status in (400, 500) or e.status is None):
                print(f"  {site['name']}: category {code}: stopped at {start} products ({e})")
                if _read_kids(site, code, st, depth):
                    print(f"  {site['name']}: category {code}: rest read through its sub-categories")
                else:
                    print(f"  {site['name']}: category {code}: no sub-categories - rest skipped")
                return
            raise
        st["requests"] += 1
        if start == 0:
            kids = JARIR_CATEGORY_TREE.get(code, [])
            label = JARIR_CATEGORY_NAMES.get(code, "")
            pad = "  " * depth
            if total >= JARIR_API_WINDOW and kids:     # >= : the API reports at most 10000, so 10000 means "10000 or more"
                print(f"  {site['name']}: {pad}category {code} {label}: {total}+ products -> "
                      f"reading its {len(kids)} sub-categories")
                _read_kids(site, code, st, depth)
                return
            if total >= JARIR_API_WINDOW:
                print(f"  {site['name']}: {pad}category {code}: {total} products, only the first "
                      f"{JARIR_API_WINDOW} can be read")
            elif depth == 0:
                print(f"  {site['name']}: category {code} {label}: {total} products")
        srcs = [h.get("_source") or {} for h in hits]
        _collect_prices(srcs)
        for o in _jarir_offers(site, srcs):
            st["offers"][o["id"]] = o
        for o in _jarir_unavailable(site, srcs):
            st.setdefault("unavail", {})[o["id"]] = o
        st["products"] += len(hits)
        start += len(hits)
        if st["requests"] % 20 == 0:
            print(f"  {site['name']}: {st['products']} products read, {len(st['offers'])} discounted so far...")
        if not hits or start >= total or start >= JARIR_API_WINDOW:
            return
        time.sleep(random.uniform(0.7, 1.6))


def scan_jarir_api(site):
    """No browser: read the products from Jarir's public API (offset based), category by category.
    Only keeps the discounted ones. A refusal (403/429) stops the scan; it never tries to get around it."""
    st = {"size": JARIR_API_PAGE_SIZE, "requests": 0, "products": 0, "offers": {}, "unavail": {}}
    problem = None
    blocked = False
    failed = []
    for code in site["api_categories"]:
        try:
            _api_collect(site, str(code), st)
        except ApiRefused as e:
            problem = e
            print(f"  {site['name']}: category {code}: {e}")
            if e.status in (403, 429):
                blocked = True
                break                              # blocked: stop, do not keep hammering
            failed.append(code)
    if failed and not blocked:                     # one more try for the categories that failed (network hiccups)
        print(f"  {site['name']}: retrying {len(failed)} failed categories in 60s...")
        time.sleep(60)
        for code in failed:
            try:
                _api_collect(site, str(code), st)
                problem = None if code == failed[-1] else problem
            except ApiRefused as e:
                problem = e
                print(f"  {site['name']}: category {code} failed again: {e}")
                if e.status in (403, 429):
                    break
    if st["products"] == 0 and problem is not None:
        raise problem
    if problem is not None:
        print(f"  {site['name']}: scan was cut short - using the {st['products']} products read so far")
    print(f"  {site['name']}: {st['products']} products read, {len(st['offers'])} discounted offers "
          f"after exclusions (no browser, {st['requests']} requests)")
    UNAVAIL_FOUND.clear()
    UNAVAIL_FOUND.update(st["unavail"])
    print(f"  {site['name']}: {len(st['unavail'])} discounted products are out of stock online (to be checked in showrooms)")
    return st["offers"]


def scan_site(browser, site):
    if site.get("kind") == "jarir":
        if site.get("api_categories"):
            try:
                return scan_jarir_api(site) or None
            except ApiRefused as e:
                print(f"  {site['name']}: API refused ({e})")
                if not JARIR_BROWSER_FALLBACK:
                    return None
                print(f"  {site['name']}: falling back to Chrome")
        return scan_jarir(browser, site)
    offers = {}
    failures = 0
    for page in range(1, PAGES + 1):
        res = None
        for _try in range(2):             # one retry if the page came back incomplete
            src = browser.source(site["url"].format(page=page), ready=lambda t, s=site: page_has_data(t, s))
            res = parse(site, src) if src else None
            if res is not None and res[1] > 0:
                break
        if res is not None and res[1] == 0 and page > 1 and site.get("kind") == "jarir":
            break                         # Jarir: a page with no products = past the last page
        if res is None or res[1] == 0:
            failures += 1
            print(f"  {site['name']} page {page}: no products found (timeout, blocked, last page, or layout differs)")
            if page == 1 or failures >= 3:
                break
            continue
        failures = 0
        for o in res[0]:
            offers[o["id"]] = o
    print(f"  {site['name']}: {len(offers)} offers after filters")
    return offers or None


PRICES_FOUND = {}     # sku -> (price, regular price, title, url): EVERY product the API returned in this scan


def _collect_prices(sources):
    for x in sources:
        try:
            sku = str(x.get("sku") or x.get("id") or "")
            price = float(x.get("final_price") or x.get("special_price") or 0)
            was = float(x.get("regular_price") or x.get("price") or price)
        except (TypeError, ValueError):
            continue
        title = x.get("name") or x.get("meta_title") or ""
        if not sku or price <= 0 or is_excluded(title):
            continue
        key = x.get("url_path") or ((x.get("url_key") or "") + ".html")
        PRICES_FOUND[sku] = (price, max(was, price), title, key)


UNAVAIL_FOUND = {}    # filled by the API scan: discounted products that are NOT in stock online


# ----------------------------- Out-of-stock offers: showroom stock (v2) ---------------
def _showroom_fetch(sku):
    """The showroom stock request the product page itself makes. -> [(centre_code, name, city_code)] of the
    showrooms that have stock (status other than OUTOFSTOCK), or None if the request failed.
    Raises ApiRefused on 403/429 (the scan of showrooms then stops; it never tries to get around it)."""
    url = SHOWROOM_API.format(sku=sku)
    data = None
    for attempt in range(3):
        try:
            req = urllib.request.Request(url, headers=dict(_API_HEADERS, Referer="https://www.jarir.com/"))
            with urllib.request.urlopen(req, timeout=60) as r:
                data = json.loads(r.read().decode("utf-8", "replace"))
            break
        except urllib.error.HTTPError as e:
            if e.code in (403, 429):
                raise ApiRefused(f"showroom API HTTP {e.code}", e.code)
            if e.code in (502, 503, 504) and attempt < 2:
                time.sleep(5 * (attempt + 1))
                continue
            return None
        except Exception:
            if attempt < 2:
                time.sleep(5 * (attempt + 1))
                continue
            return None
    rows = data.get("data") if isinstance(data, dict) else None
    if not isinstance(rows, list) or (isinstance(data, dict) and data.get("success") is False):
        return None
    return [(str(r.get("centre_code") or ""), (r.get("name") or "").strip(), str(r.get("city_code") or ""))
            for r in rows if isinstance(r, dict)
            and str(r.get("availability_status") or "").upper() not in ("OUTOFSTOCK", "")]


def _load_cache():
    try:
        return json.loads(SHOWROOM_CACHE_FILE.read_text(encoding="utf-8")) if SHOWROOM_CACHE_FILE.exists() else {}
    except Exception:
        return {}


def _save_cache(cache):
    cut = time.time() - 24 * 3600
    cache = {k: v for k, v in cache.items() if v.get("t", 0) >= cut}
    SHOWROOM_CACHE_FILE.write_text(json.dumps(cache, ensure_ascii=False), encoding="utf-8")


def showroom_status(o, cache, stats):
    """-> {"all": [...], "shown": [...]} (showrooms with stock: everywhere / in the wanted cities), or None if the
    product could not be checked this time."""
    allv, ok = [], False
    for sku, label in o["skus"]:
        ent = cache.get(sku)
        if ent and time.time() - ent["t"] < SHOWROOM_CACHE_MIN * 60:
            lim = ent["lim"]
        else:
            lim = _showroom_fetch(sku)
            stats["requests"] += 1
            time.sleep(random.uniform(1.0, 2.0))
            if lim is None:
                continue
            cache[sku] = {"t": time.time(), "lim": lim}
        ok = True
        allv += [(c, n, ci, label) for c, n, ci in lim]
    if not ok:
        return None
    wanted = {c.upper() for c in SHOWROOM_CITIES}
    return {"all": allv, "shown": [v for v in allv if not wanted or v[2].upper() in wanted]}


def load_extra():
    try:
        d = json.loads(SHOWROOM_FILE.read_text(encoding="utf-8")) if SHOWROOM_FILE.exists() else {}
    except Exception:
        d = {}
    return {"sh": d.get("sh", []), "un": d.get("un", [])}


def process_extras(now_dt, state):
    """Checks the out-of-stock-online offers against the showroom stock API and sorts them into
    'limited in a showroom' (sh) and 'unavailable everywhere' (un). -> (new offers of the first kind, changed?)"""
    cands = unique(sorted(UNAVAIL_FOUND.values(), key=lambda o: -o["pct"]))[:SHOWROOM_MAX_CHECKS]
    if not cands:
        return [], False
    cache, stats = _load_cache(), {"requests": 0}
    sh, un, checked = [], [], set()
    try:
        for o in cands:
            res = showroom_status(o, cache, stats)
            if res is None:
                continue
            checked.add(o["id"])
            if res["shown"]:
                if o["pct"] >= SHOWROOM_MIN_PCT:
                    names = [n + (f" ({lab})" if lab else "") for c, n, ci, lab in res["shown"]]
                    text = f"{len(names)} معرض: " + " | ".join(names[:6]) + (f" | +{len(names) - 6}" if len(names) > 6 else "")
                    sh.append(dict(o, codes=sorted({c for c, n, ci, lab in res["shown"]}), sh=text))
            elif not res["all"] and o["pct"] >= UNAVAIL_MIN_PCT:
                un.append(dict(o))
    except ApiRefused as e:
        print(f"  showroom stock: {e} - stopping the showroom checks for this scan")
    finally:
        _save_cache(cache)
    print(f"  showroom stock: {len(checked)} of {len(cands)} out-of-stock offers checked ({stats['requests']} requests, "
          f"the rest from cache): {len(sh)} limited in showrooms, {len(un)} unavailable everywhere")

    stamp = now_dt.isoformat(timespec="minutes")
    old = load_extra()
    old_sh, old_un = {o["id"]: o for o in old["sh"]}, {o["id"]: o for o in old["un"]}
    failed = {o["id"] for o in cands} - checked            # could not be checked now: keep what the page showed
    cut7 = (now_dt - datetime.timedelta(days=7)).isoformat(timespec="minutes")
    prev_sh, prev_un = state.get("Jarir:limited"), state.get("Jarir:unavail")   # None = first run: baseline only
    new_sh = []
    for o in sh:
        was = old_sh.get(o["id"], {})
        o["found"], o["new_at"] = was.get("found", stamp), was.get("new_at", "")
        before = (prev_sh or {}).get(o["id"])
        if prev_sh is not None and (before is None or set(o["codes"]) - set(before.get("codes", []))):
            o["new_at"] = stamp
            new_sh.append(o)
    for o in un:
        was = old_un.get(o["id"], {})
        o["found"], o["new_at"] = was.get("found", stamp), was.get("new_at", "")
        before = (prev_un or {}).get(o["id"])
        if prev_un is not None and (before is None or o["price"] < before.get("price", 1e18)):
            o["new_at"] = stamp
    sh += [old_sh[i] for i in failed if i in old_sh]
    un += [old_un[i] for i in failed if i in old_un]
    sh.sort(key=lambda o: (-o["pct"], o["title"]))
    un.sort(key=lambda o: (-o["pct"], o["title"]))
    SHOWROOM_FILE.write_text(json.dumps({"sh": sh, "un": un}, ensure_ascii=False), encoding="utf-8")

    def keep(prev, cur):
        out = {k: v for k, v in (prev or {}).items() if k not in checked and v.get("t", "") >= cut7}
        out.update(cur)
        return out
    state["Jarir:limited"] = keep(prev_sh, {o["id"]: {"codes": o["codes"], "t": stamp} for o in sh if "codes" in o})
    state["Jarir:unavail"] = keep(prev_un, {o["id"]: {"price": o["price"], "t": stamp} for o in un})
    save_state(state)
    return new_sh, True


PRICE_LAST_FILE = DATA / "last_prices.json"       # sku -> [price, regular price]
PRICE_LOG_FILE = DATA / "price_history.csv"      # t,sku,price,was   (one row per change)
PRODUCTS_FILE = DATA / "products.json"           # sku -> [title, url path]


def record_prices():
    """Append a row for every product that is new or whose price changed since the last scan."""
    if not PRICES_FOUND:
        return
    def load(p):
        try:
            return json.loads(p.read_text(encoding="utf-8")) if p.exists() else {}
        except Exception:
            return {}
    last, prods = load(PRICE_LAST_FILE), load(PRODUCTS_FILE)
    t = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
    rows, changed = [], 0
    for sku, (price, was, title, key) in PRICES_FOUND.items():
        old = last.get(sku)
        if old is None or old[0] != price or old[1] != was:
            rows.append(f"{t},{sku},{price:g},{was:g}\n")
            if old is not None:
                changed += 1
            last[sku] = [price, was]
        if sku not in prods:
            prods[sku] = [title, key]
    if rows:
        new_file = not PRICE_LOG_FILE.exists()
        with PRICE_LOG_FILE.open("a", encoding="utf-8") as f:
            if new_file:
                f.write("t,sku,price,was\n")
            f.writelines(rows)
        PRICE_LAST_FILE.write_text(json.dumps(last, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
        PRODUCTS_FILE.write_text(json.dumps(prods, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    print(f"  price history: {len(PRICES_FOUND)} products seen, {len(rows)} rows written ({changed} price changes)")


PAGE_OPENED = False   # the results page is opened once per run; it refreshes itself afterwards


def alert_ok(o):
    """Notifications only for offers at or above the alert discount."""
    return o["pct"] >= MIN_PCT_BY_SITE.get(o["site"], MIN_DISCOUNT_PCT)


def run_once(browser):
    global PAGE_OPENED
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    print(f"[{now}] scanning...")
    UNAVAIL_FOUND.clear()
    PRICES_FOUND.clear()
    reload_excluded_words()        # pick up edits to excluded_words.txt
    state = load_state()           # {site_name: {offer_id: last_price}}
    all_new, all_drops, current = [], [], []
    for site in SITES:
        try:
            offers = scan_site(browser, site)
        except Exception as e:
            print(f"  {site['name']} error: {e}")
            continue
        if not offers:
            continue
        current += [o for o in offers.values() if o["pct"] >= COLLECT_MIN_PCT]
        seen = state.get(site["name"])
        if seen is None:           # first time for this site = no "new" flags, everything is just listed
            state[site["name"]] = {k: v["price"] for k, v in offers.items()}
            notify(f"{site['name']} monitoring started", f"Baseline saved: {len(offers)} offers.")
            continue
        all_new += [o for k, o in offers.items() if k not in seen and o["pct"] >= COLLECT_MIN_PCT]
        all_drops += [o for k, o in offers.items() if k in seen and o["price"] < seen[k]
                      and o["pct"] >= COLLECT_MIN_PCT]
        seen.update({k: v["price"] for k, v in offers.items()})
        save_state(state)
    save_state(state)

    new_limited, extras_changed = [], False
    try:
        new_limited, extras_changed = process_extras(datetime.datetime.now(), state)
    except Exception as e:
        print(f"  showroom stock error: {type(e).__name__}: {e}")

    try:
        record_prices()
    except Exception as e:
        print(f"  price history error: {type(e).__name__}: {e}")

    all_new.sort(key=lambda o: -o["pct"])
    known = {dedupe_key(h) for h in load_history()}
    all_new = [dict(o, kind="nw") for o in unique(all_new) if dedupe_key(o) not in known]   # drop duplicates/variants
    all_drops = [dict(o, kind="dr") for o in unique(all_drops) if dedupe_key(o) not in known]
    new_alerts = [o for o in all_new if alert_ok(o)]
    drop_alerts = [o for o in all_drops if alert_ok(o)]
    with LOG_FILE.open("a", encoding="utf-8") as f:
        for o in new_alerts:
            line = f"{now} NEW [{o['site']}] {o['pct']}% {o['was']:g}->{o['price']:g} SAR {o['title']} {o['url']}"
            print(line)
            f.write(line + "\n")
    if new_alerts:
        notify(f"{len(new_alerts)} new offers",
               "\n".join(f"[{o['site']}] {o['pct']}% - {o['title'][:45]}" for o in new_alerts[:3]))
    if new_limited:
        with LOG_FILE.open("a", encoding="utf-8") as f:
            for o in new_limited:
                line = (f"{now} SHOWROOM [{o['site']}] {o['pct']}% {o['was']:g}->{o['price']:g} SAR {o['title']} "
                        f"| {o['sh']} {o['url']}")
                print(line)
                f.write(line + "\n")
        notify(f"{len(new_limited)} out-of-stock offers in showrooms",
               "\n".join(f"{o['pct']}% - {o['title'][:45]}" for o in new_limited[:3]))
    if current or all_new or all_drops or extras_changed:
        update_results(all_new + all_drops, datetime.datetime.now(), current)
        if OPEN_IN_BROWSER and not PAGE_OPENED:
            open_urls([HTML_FILE.as_uri()])
            PAGE_OPENED = True
    if drop_alerts:
        notify(f"{len(drop_alerts)} price drops",
               "\n".join(f"[{o['site']}] {o['title'][:45]} -> {o['price']:g}" for o in drop_alerts[:3]))


def dump_pages():
    DUMP_DIR.mkdir(exist_ok=True)
    browser = Browser()
    try:
        for site in SITES:
            if site.get("kind") == "jarir":
                offers = scan_site(browser, site)
                print(site["name"], "->", f"{len(offers)} offers (first page + scrolling)" if offers else "NO DATA")
                continue
            src = browser.source(site["url"].format(page=1), ready=lambda t, s=site: page_has_data(t, s))
            if not src:
                print(site["name"], "-> NO DATA (page did not load)")
                continue
            (DUMP_DIR / f"{site['name']}.html").write_text(src, encoding="utf-8")
            res = parse(site, src)
            print(site["name"], "->", "parsed %d offers of %d items" % (len(res[0]), res[1]) if res else "NO DATA")
    finally:
        browser.stop()


def main():
    browser = Browser()
    try:
        while True:
            try:
                run_once(browser)
            except Exception as e:
                print("scan error:", e)
            time.sleep(CHECK_EVERY_MIN * 60)
    finally:
        browser.stop()


def check_sku(sku):
    """python script.py --check 683540 : the showrooms the site says have stock of one item number."""
    try:
        lim = _showroom_fetch(sku)
    except ApiRefused as e:
        print(e)
        return
    if lim is None:
        print("the showroom request failed")
        return
    print(f"{sku}: {len(lim)} showrooms with stock")
    for c, n, ci in lim:
        print(f"  {c}  {ci:4}  {n}")


if __name__ == "__main__":
    args = sys.argv[1:]
    if "--cats" in args:
        SITES[0]["api_categories"] = [c.strip() for c in args[args.index("--cats") + 1].split(",") if c.strip()]
    if len(args) > 1 and args[0] == "--test":
        html = Path(args[1]).read_text(encoding="utf-8")
        want = "jarir" if "__NUXT_DATA__" in html else "landmark"
        res = parse(next(s for s in SITES if s["kind"] == want), html)
        print(f"{res[1]} items, {len(res[0])} kept")
        for o in res[0][:8]:
            print(o["pct"], o["was"], o["price"], o["title"][:50])
    elif args and args[0] == "--dump":
        dump_pages()
    elif "--check" in args:
        check_sku(args[args.index("--check") + 1])
    elif "--once" in args:
        b = Browser()
        try:
            run_once(b)
        finally:
            b.stop()
    else:
        main()
