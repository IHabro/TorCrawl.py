#!/usr/bin/python
import http.client
import os
import re
import socket
import ssl
import sys
import datetime
import threading
import time
import urllib.request
from urllib.parse import urlparse, urljoin, parse_qsl, urlencode
from collections import defaultdict, deque
from urllib.error import HTTPError, URLError

from bs4 import BeautifulSoup
from modules.checker import make_request
from modules.checker import strip_www

DEFAULT_URL_REGEX = r'(?:(?:https?|ftp|file):\/\/|www\.)[^\s"\'<>]+'
DEFAULT_REGEX_FILE = os.path.abspath(
    os.path.join(os.path.dirname(__file__), os.pardir, 'res', 'regex_patterns.txt')
)
IMAGE_EXTS = ('.jpg', '.jpeg', '.png', '.gif', '.webp', '.svg', '.bmp')

# Compiled once at import time — used by is_darkweb_url() for every link check.
_BASE32_RE = re.compile(r'^[a-z2-7]+$')


def clean_domain(url):
    """Strip protocol, www., and subdomains from a URL.

    Returns the bare base domain in 'domain.tld' format — e.g. 'example.onion'.
    This is the canonical key used by the outer domain queue for deduplication,
    so that http://www.example.onion, http://sub.example.onion and
    http://example.onion/page all map to the same domain token.

    :param url: String - any URL or bare hostname.
    :return: String - bare base domain, or '' on parse failure.
    """
    try:
        parsed = urlparse(url)
        host = parsed.netloc.lower()
        if not host:
            # Handle bare hostnames without a scheme
            host = url.lower().split('/')[0]
        host = host.split(':')[0]           # strip optional port
        if host.startswith('www.'):
            host = host[4:]
        # Keep only the last two dot-separated labels: sub.example.onion → example.onion
        parts = host.split('.')
        if len(parts) > 2:
            host = '.'.join(parts[-2:])
        return host
    except Exception:
        return ''


class Crawler:
    # Maps each resource category to the suffix of its log file.
    # Used by _record_resource() to build the full path without repeating
    # os.path.join(...) inline in every branch of excludes().
    _CATEGORY_LOG = {
        "images":         '_images.txt',
        "scripts":        '_scripts.txt',
        "external_links": '_ext-links.txt',
        "telephones":     '_telephones.txt',
        "emails":         '_mails.txt',
        "files":          '_files.txt',
    }

    # Query parameters that indicate pagination — stripped during deduplication
    # so that ?page=1 and ?page=2 are treated as the same resource.
    PAGINATION_PARAMS = frozenset({
        'page', 'p', 'pg', 'pag', 'pagina',
        'offset', 'start', 'from', 'skip',
        'pagenum', 'pageindex', 'pagenumber', 'page_number',
        'currentpage', 'current_page',
        'num', 'no',
        'limitstart',   # Joomla
        'paged',        # WordPress
    })

    def __init__(self, website, c_pause, out_path, logs, verbose,
                 random_ua=False, random_proxy=False, max_domains=10, max_pages=10,
                 extract=False, seed_urls=None):
        self.website = website
        self.max_domains = max_domains  # 0 = unlimited
        self.max_pages = max_pages      # 0 = unlimited
        self.extract = extract          # save raw HTML to disk during crawl
        self.seed_urls = seed_urls or []
        # Populated by crawl() — available via export_payload() afterwards
        self.crawled_domains = []       # domains successfully processed
        self.pending_domains = []       # domains in queue when crawl stopped
        self.out_path = out_path
        self.c_pause = c_pause
        self.logs = logs
        self.verbose = verbose
        self.random_ua = random_ua
        self.random_proxy = random_proxy
        self.regex_patterns = self._load_regex_patterns()
        self.timestamp = datetime.datetime.now().strftime("%y%m%d")
        # Base domain uses clean_domain so subdomains are treated as same-domain
        self.base_domain = clean_domain(self.website)
        self.findings = {
            "links": set(),
            "external_links": set(),
            "images": set(),
            "scripts": set(),
            "telephones": set(),
            "emails": set(),
            "files": set(),
        }
        self.normalized_links = set()
        # Both logged and resources are keyed identically to _CATEGORY_LOG
        self.logged    = {cat: set()            for cat in self._CATEGORY_LOG}
        self.resources = {cat: defaultdict(set) for cat in self._CATEGORY_LOG}
        self.edges = set()
        self.titles = {}
        # Threading event — set externally (e.g. by keylistener) to request
        # a graceful early stop.  crawl() checks this at every iteration of
        # both the inner and outer loops, then falls through to the normal
        # export path so no data is lost.
        self.stop_requested = threading.Event()
        self.ssl_ctx = ssl.create_default_context()
        self.ssl_ctx.check_hostname = False
        self.ssl_ctx.verify_mode = ssl.CERT_NONE

    # ── Startup ────────────────────────────────────────────────────────────────

    def _load_regex_patterns(self):
        """Load regex patterns from res/regex_patterns.txt plus the default URL pattern.

        :return: List[re.Pattern] - compiled patterns.
        """
        patterns = [DEFAULT_URL_REGEX]
        try:
            if os.path.exists(DEFAULT_REGEX_FILE):
                with open(DEFAULT_REGEX_FILE, 'r', encoding='UTF-8') as f:
                    for line in f:
                        stripped = line.strip()
                        if stripped and not stripped.startswith('#'):
                            patterns.append(stripped)
        except OSError as err:
            print(f"## Unable to read regex pattern file {DEFAULT_REGEX_FILE}: {err}")

        compiled = []
        for pattern in patterns:
            try:
                compiled.append(re.compile(pattern, re.IGNORECASE))
            except re.error as err:
                print(f"## Skipping invalid regex pattern '{pattern}': {err}")
        return compiled

    # ── File I/O ───────────────────────────────────────────────────────────────

    def _domain_out_path(self, url):
        """Return the per-domain output subfolder path without creating it.

        Uses clean_domain so that all subdomains of a site share one folder.
        The folder is created by _save_page() only when content is ready to write.

        :param url: String - any URL whose domain should be used.
        :return: String - path to the domain subfolder.
        """
        domain = clean_domain(url) or self.base_domain
        return os.path.join(self.out_path, domain)

    def _save_page(self, url, raw_content):
        """Save raw page content to the per-domain subfolder.

        Filename is derived from the last path segment of the URL,
        falling back to 'index.htm' for root paths.
        A numeric suffix is appended on filename collision.

        :param url: String - URL of the fetched page.
        :param raw_content: bytes - raw HTTP response body.
        """
        try:
            page_name = urlparse(url).path.rsplit('/', 1)[-1]
            filename = page_name if page_name else "index.htm"
        except Exception:
            filename = "index.htm"

        domain_path = self._domain_out_path(url)
        try:
            os.makedirs(domain_path, exist_ok=True)
        except OSError as err:
            msg = f"## ERROR creating folder {domain_path} for {url}: {err}"
            print(msg)
            self._log_file_error(msg)
            return

        filepath = os.path.join(domain_path, filename)
        if os.path.exists(filepath):
            base, ext = os.path.splitext(filename)
            counter = 1
            while os.path.exists(filepath):
                filepath = os.path.join(domain_path, f"{base}({counter}){ext}")
                counter += 1

        try:
            with open(filepath, 'wb') as f:
                f.write(raw_content)
            if self.verbose:
                print(f"## Saved: {filepath}")
        except IOError as err:
            msg = f"## ERROR saving {url} to {filepath}: {err}"
            print(msg)
            self._log_file_error(msg)

    # ── Logging ────────────────────────────────────────────────────────────────

    def _log_error(self, msg, filename):
        """Append a timestamped error message to a log file in out_path.

        Shared implementation used by _log_fetch_error() and _log_file_error().
        Does nothing when self.logs is False.

        :param msg: String - error message (should already be printed by caller).
        :param filename: String - log filename (e.g. 'fetchError.log').
        """
        if not self.logs:
            return
        log_path = os.path.join(self.out_path, filename)
        try:
            os.makedirs(self.out_path, exist_ok=True)
            with open(log_path, 'a+', encoding='UTF-8') as f:
                f.write(f"{datetime.datetime.now()} {msg}\n")
        except IOError as err:
            print(f"## WARNING: Could not write to {log_path}: {err}")

    def _log_fetch_error(self, msg):
        """Log a network/fetch error to fetchError.log."""
        self._log_error(msg, 'fetchError.log')

    def _log_file_error(self, msg):
        """Log a file I/O error to fileError.log."""
        self._log_error(msg, 'fileError.log')

    def _log_once(self, category, link, filepath):
        """Write a categorised link to its log file once (deduped by normalised URL).

        :param category: String - findings category key (e.g. 'images').
        :param link: String - link value to log.
        :param filepath: String - destination log file path.
        """
        norm = self._normalize_for_dedupe(link)
        if norm in self.logged.get(category, set()):
            return
        self.logged.setdefault(category, set()).add(norm)
        try:
            os.makedirs(os.path.dirname(filepath), exist_ok=True)
            with open(filepath, 'a+', encoding='UTF-8') as f:
                f.write(str(link) + '\n')
        except IOError as err:
            msg = f"## ERROR writing {category} link to {filepath}: {err}"
            print(msg)
            self._log_file_error(msg)

    def _record_resource(self, category, link, source):
        """Record a non-page resource into findings, resources, and its log file.

        Centralises the three-step pattern that was previously repeated for every
        resource category in excludes():
            _log_once  +  findings.add  +  resources[category][source].add

        :param category: String - key from _CATEGORY_LOG (e.g. 'images').
        :param link: String - resource URL / value (already stripped of scheme prefix
                    for tel: and mailto: links).
        :param source: String - URL of the page the resource was found on.
        """
        filepath = os.path.join(self.out_path, self.timestamp + self._CATEGORY_LOG[category])
        self._log_once(category, link, filepath)
        self.findings[category].add(str(link))
        self.resources[category][source].add(str(link))

    # ── HTTP ───────────────────────────────────────────────────────────────────

    def _httpget(self, url):
        """Fetch *url* and return its raw response body.

        All network and I/O errors are caught, printed, and logged internally
        so callers only need to check for a None return value.

        :param url: String - URL to fetch.
        :return: (bytes, str) tuple — (raw_content, html_content) on success,
                 or (None, None) on any error.
        """

        socketTimeout = 10

        try:
            response = make_request(url, self.random_ua, self.random_proxy,
                                    timeout=socketTimeout, ssl_ctx=self.ssl_ctx)
        except socket.timeout:
            msg = f"## TIMEOUT fetching {url} (timeout={socketTimeout}s)"
            print(msg); self._log_fetch_error(msg)
            return None, None
        except ConnectionResetError as e:
            msg = f"## CONNECTION RESET by {url}: {e}"
            print(msg); self._log_fetch_error(msg)
            return None, None
        except OSError as e:
            msg = f"## SOCKET ERROR fetching {url}: {e}"
            print(msg); self._log_fetch_error(msg)
            return None, None
        except http.client.IncompleteRead as e:
            msg = f"## INCOMPLETE READ fetching {url}: {e}"
            print(msg); self._log_fetch_error(msg)
            return None, None
        except HTTPError as e:
            msg = f"## HTTP ERROR {e.code} fetching {url}: {e.reason}"
            print(msg); self._log_fetch_error(msg)
            return None, None
        except URLError as e:
            msg = f"## URL ERROR fetching {url}: {e.reason}"
            print(msg); self._log_fetch_error(msg)
            return None, None
        except Exception as e:
            msg = f"## UNEXPECTED ERROR fetching {url}: {type(e).__name__}: {e}"
            print(msg); self._log_fetch_error(msg)
            return None, None

        # response.read() může blokovat i přes nastavený socket timeout,
        # protože SSL/SOCKS vrstvy timeout spolehlivě nepropagují.
        # Spustíme read() ve vlastním vlákně a tvrdě přerušíme po socketTimeout.
        _read_result = [None]
        _read_exc    = [None]

        def _do_read():
            try:
                _read_result[0] = response.read()
            except Exception as e:          # noqa – zachytíme cokoli z vlákna
                _read_exc[0] = e

        # Dark web tolerance: read timeout je 2× socket timeout (= 20 s),
        # aby pomalé .onion servery dostaly dostatek času dodat tělo odpovědi.
        _read_timeout = 2 * socketTimeout

        _read_thread = threading.Thread(target=_do_read, daemon=True)
        _read_thread.start()
        _read_thread.join(timeout=_read_timeout)

        if _read_thread.is_alive():
            # Vlákno stále běží — tvrdě zavřeme spojení, aby se odblokoval read()
            try:
                response.close()
            except Exception:
                pass
            msg = f"## TIMEOUT reading response body from {url} (>{_read_timeout}s)"
            print(msg); self._log_fetch_error(msg)
            return None, None

        if _read_exc[0] is not None:
            e = _read_exc[0]
            if isinstance(e, socket.timeout):
                msg = f"## TIMEOUT reading response body from {url}"
            elif isinstance(e, http.client.IncompleteRead):
                msg = f"## INCOMPLETE READ of response body from {url}: {e}"
            elif isinstance(e, OSError):
                msg = f"## SOCKET ERROR reading response body from {url}: {e}"
            else:
                msg = f"## UNEXPECTED ERROR reading response body from {url}: {type(e).__name__}: {e}"
            print(msg); self._log_fetch_error(msg)
            return None, None

        raw = _read_result[0]

        try:
            html = raw.decode('utf-8', errors='ignore') if isinstance(raw, (bytes, bytearray)) else str(raw)
        except Exception as e:
            msg = f"## UNEXPECTED ERROR decoding response body from {url}: {type(e).__name__}: {e}"
            print(msg); self._log_fetch_error(msg)
            return None, None
        
        return raw, html

    # ── Link extraction ────────────────────────────────────────────────────────

    def _extract_links(self, soup, html_content, source_url):
        """Extract all navigable page links from parsed HTML and the raw HTML string.

        Scans <a> and <area> href attributes first, then sweeps the raw HTML with
        every loaded regex pattern.  Non-page resources (images, scripts, emails,
        files, telephones, external links) are categorised and logged as a side
        effect via excludes().

        :param soup: BeautifulSoup - parsed HTML document.
        :param html_content: String - raw HTML text (for regex sweep).
        :param source_url: String - URL of the page being parsed (for edge tracking).
        :return: set of canonicalised, non-excluded link strings.
        """
        links = set()

        for tag in soup.find_all('a') + soup.find_all('area'):
            link = tag.get('href')
            if self.excludes(link, source_url):
                continue
            ver_link = self.canonical(link)
            if ver_link:
                self._add_link(ver_link, source_url, links)

        for pattern in self.regex_patterns:
            for match in pattern.finditer(html_content):
                link = match.group(0).rstrip('),.;\'"')
                if link.startswith('www.'):
                    link = f"https://{link}"
                if self.excludes(link, source_url):
                    continue
                ver_link = self.canonical(link)
                if ver_link:
                    self._add_link(ver_link, source_url, links)

        return links

    # ── Queue helpers ──────────────────────────────────────────────────────────

    # Přípony souborů, které se nikdy nestahují do inner queue.
    # Komprimované archivy a velké datové soubory — crawlovat je nemá smysl
    # a zbytečně by blokovaly síťové připojení i timeout.
    _SKIP_EXTENSIONS = frozenset({
        # Archivy / komprimované soubory
        '.zip', '.z', '.gz', '.bz2', '.xz', '.zst',
        '.rar', '.7z', '.tar', '.tgz', '.tbz2', '.cab',
        '.iso', '.img', '.dmg',
        # Velké datové soubory
        '.csv', '.tsv',
        '.xlsx', '.xls', '.xlsm',
        '.db', '.sqlite', '.sqlite3',
        '.parquet', '.feather', '.avro', '.orc',
        '.json', '.jsonl', '.ndjson',
        '.xml',
        '.pdf'
    })

    def _add_to_inner_queue(self, url, inner_queue, queued_inner, visited):
        """Add *url* to the inner BFS queue if it has not been visited or queued.

        The inner queue operates on full URLs (including subdomains and path) so
        every distinct page of a domain is fetched at most once per crawl session.
        URLs pointing to compressed archives or large data files (see
        _SKIP_EXTENSIONS) are silently ignored — they are not crawlable pages.

        :param url: String - candidate URL to enqueue.
        :param inner_queue: deque - active inner BFS queue.
        :param queued_inner: set - URLs already added to inner_queue this domain.
        :param visited: set - globally visited URLs.
        :return: Boolean - True if enqueued, False if already known or skipped.
        """
        # Extrahujeme cestu bez query stringu a fragmentu, pak zjistíme příponu.
        try:
            path = urlparse(url).path.lower()
        except Exception:
            path = url.lower()
        # Odsekneme případný query string, který by mohl obsahovat tečku.
        bare_path = path.split('?', 1)[0].split('#', 1)[0]
        ext = os.path.splitext(bare_path)[1]   # vrátí např. '.zip' nebo ''
        if ext in self._SKIP_EXTENSIONS:
            return False

        if url not in visited and url not in queued_inner:
            queued_inner.add(url)
            inner_queue.append(url)
            return True
        return False

    def _add_to_outer_queue(self, url, domain_queue, queued_domains, visited):
        """Add *url* to the outer domain queue if its clean base domain is new.

        Deduplication is performed against the clean base domain (protocol,
        www., and subdomains stripped) so that http://sub.example.onion and
        http://example.onion/page are treated as the same domain.

        :param url: String - seed URL for the candidate domain.
        :param domain_queue: deque - outer domain queue.
        :param queued_domains: set - clean domains already in the outer queue.
        :param visited: set - globally visited URLs.
        :return: Boolean - True if the domain was newly added, False otherwise.
        """
        domain = clean_domain(url)
        if domain and domain not in queued_domains and url not in visited:
            queued_domains.add(domain)
            domain_queue.append(url)
            return True
        return False

    # ── URL helpers ────────────────────────────────────────────────────────────

    @staticmethod
    def is_darkweb_url(url):
        """Return True if *url* points to a Tor hidden service (.onion domain).

        Validates both legacy v2 (16-char base32) and current v3 (56-char base32)
        .onion hostnames.  The check is applied only to the netloc so that
        surface-web URLs containing '.onion' in a query parameter are never
        mistakenly treated as dark-web targets.

        :param url: String — raw URL to test.
        :return: Boolean
        """
        try:
            parsed = urlparse(url)
        except Exception:
            return False

        if parsed.scheme not in ('http', 'https', 'irc', 'ircs', 'xmpp'):
            return False

        host = parsed.netloc.lower().split(':')[0]

        if not (host.endswith('.onion') or host.endswith('.onion/')
                or host.endswith('.onion\\')):
            return False

        # Validate the onion label (rightmost label before .onion)
        onion_label = host[:-6].rsplit('.', 1)[-1]
        if len(onion_label) in (16, 56) and _BASE32_RE.match(onion_label):
            return True
        # Accept non-standard / unknown-length .onion hostnames — the .onion TLD
        # check above is the hard gate.
        return True

    def excludes(self, link, source_url=None):
        """Categorise and exclude non-page links.

        Images, scripts, tel: links, mailto: links and downloadable files are
        logged into their respective category files and excluded from crawling.
        External non-.onion links are also excluded.  External .onion links
        return False (= not excluded) so the caller can route them to the outer
        domain queue.

        :param link: String - raw href value from the page.
        :param source_url: String - URL of the page the link was found on.
        :return: Boolean - True means skip this link; False means keep crawling.
        """
        # Guard None early — BeautifulSoup returns None when href is missing.
        if link is None:
            return True
        # Fragment-only anchors never point to a new page.
        if '#' in link:
            return True

        source = source_url or self.website

        # Determine whether this absolute URL belongs to the same base domain.
        same_domain = False
        if link.startswith(('http://', 'https://')):
            try:
                same_domain = clean_domain(link) == self.base_domain
            except ValueError:
                return True

        if self._is_image_link(link):
            self._record_resource("images", link, source)
            return True
        if re.search(r'^.*\.(js|mjs|ts|jsx|tsx)$', link, re.IGNORECASE):
            self._record_resource("scripts", link, source)
            return True
        if link.startswith('http') and not same_domain:
            self._record_resource("external_links", link, source)
            return not self.is_darkweb_url(link)   # False = crawl it, True = skip it
        if link.startswith('tel:'):
            self._record_resource("telephones", link.replace('tel:', '', 1), source)
            return True
        if link.startswith('mailto:'):
            self._record_resource("emails", link.replace('mailto:', '', 1), source)
            return True
        if re.search(r'^.*\.(pdf|doc)$', link, re.IGNORECASE):
            # Files are tracked globally only — no per-source resource mapping.
            filepath = os.path.join(self.out_path, self.timestamp + self._CATEGORY_LOG["files"])
            self._log_once("files", link, filepath)
            self.findings["files"].add(str(link))
            return True

    def canonical(self, link):
        """Return the canonical absolute URL for *link* relative to self.website.

        :param link: String - raw href value.
        :return: String - absolute URL, or None if the link cannot be resolved.
        """
        if link.startswith(self.website):
            return link
        if link.startswith(('http://', 'https://')):
            try:
                candidate_domain = clean_domain(link)
                if candidate_domain == self.base_domain:
                    return link
            except ValueError:
                return None
            return link
        if link.startswith('/'):
            return self.website.rstrip('/') + link
        if not link.startswith('http') and not link.startswith('//'):
            base = self.website if self.website.endswith('/') else self.website + '/'
            return urljoin(base, link)
        if link.startswith('//'):
            scheme = urlparse(self.website).scheme
            return f"{scheme}:{link}"

    # ── Deduplication ──────────────────────────────────────────────────────────

    def _normalize_for_dedupe(self, url):
        """Normalise URL for deduplication.

        - Lower-cases and strips www. from the host.
        - Strips pagination query parameters (page, offset, p, …).
        - Non-pagination parameters (e.g. ?category=x) are preserved.
        """
        try:
            parsed = urlparse(url)
            netloc = strip_www(parsed.netloc.lower())
            if parsed.query:
                filtered = [(k, v) for k, v in parse_qsl(parsed.query)
                            if k.lower() not in self.PAGINATION_PARAMS]
                new_query = urlencode(filtered)
            else:
                new_query = ''
            return parsed._replace(netloc=netloc, query=new_query).geturl()
        except ValueError:
            return url.strip().lower()

    def _add_link(self, ver_link, source_url, lst):
        """Add a link to the working set with normalised-URL deduplication.

        Adds to self.findings['links'], self.normalized_links, the caller's
        local set *lst*, and always records the directed edge regardless of
        whether the link was already known.

        :param ver_link: String - canonicalised target URL.
        :param source_url: String - URL of the page the link was found on.
        :param lst: set - caller's local link collection for this page.
        """
        norm = self._normalize_for_dedupe(ver_link)
        if norm not in self.normalized_links:
            self.normalized_links.add(norm)
            lst.add(ver_link)
            self.findings["links"].add(ver_link)
        if source_url and ver_link:
            self.edges.add((source_url, ver_link))

    # ── Core crawler ───────────────────────────────────────────────────────────

    def crawl(self):
        """Two-level BFS crawler.

        Outer loop (domain_queue):
            One iteration per domain.  A domain is fully exhausted before
            the next one is started.  Deduplication key: clean base domain
            (clean_domain()).

        Inner loop (inner_queue):
            BFS over all subpages of the current domain.  External .onion
            links discovered here are collected and promoted to domain_queue
            once the inner loop finishes.

        :return: List[str] - ordered list of all discovered links.
        """
        visited = set()
        queued_domains = {clean_domain(self.website)}
        domain_queue = deque([self.website])

        # Pre-populate outer queue from additional seed URLs (e.g. --input file).
        for seed in self.seed_urls:
            seed = seed.strip()
            if not seed:
                continue
            if not self.is_darkweb_url(seed):
                print(f"## Skipping non-.onion seed URL: {seed}")
                continue
            self._add_to_outer_queue(seed, domain_queue, queued_domains, visited)

        ord_lst = [self.website]
        self.findings["links"].add(self.website)
        self.normalized_links.add(self._normalize_for_dedupe(self.website))

        max_hint = f", max domains: {self.max_domains}" if self.max_domains else ""
        print(f"## Crawler started from {self.website}, {self.c_pause}s delay{max_hint}.")

        domains_crawled = 0

        # ── Outer loop: one iteration = one domain ────────────────────────────
        while domain_queue:
            if self.stop_requested.is_set():
                print("## User requested stop — exiting outer queue.")
                break

            if self.max_domains and domains_crawled >= self.max_domains:
                print(f"## Reached max domains limit ({self.max_domains}), stopping outer queue.")
                break

            seed_url = domain_queue.popleft()
            if seed_url in visited:
                continue

            current_base = clean_domain(seed_url)
            inner_queue = deque([seed_url])
            queued_inner = {seed_url}
            pending_external = {}   # clean_domain → first seen seed URL
            pages_in_domain = 0

            # ── Inner loop: exhaust all subpages of current domain ─────────────
            while inner_queue:
                if self.stop_requested.is_set():
                    print("## User requested stop — exiting inner queue.")
                    break

                if self.max_pages and pages_in_domain >= self.max_pages:
                    print(f"## Reached max pages limit ({self.max_pages}), stopping inner queue.")
                    break

                item = inner_queue.popleft()
                if item in visited:
                    continue
                visited.add(item)

                if self.verbose:
                    sys.stdout.write(
                        f"-- inner queue: [{pages_in_domain}/"
                        f"{len(inner_queue) + pages_in_domain}]/{self.max_pages} | "
                        f"domain queue: [{domains_crawled}/"
                        f"{len(domain_queue) + domains_crawled}]/{self.max_domains} | "
                        f"workin on: {item}\n"
                    )
                    sys.stdout.flush()

                # Fetch page
                raw_content, html_content = self._httpget(item)
                if raw_content is None:
                    continue

                pages_in_domain += 1

                # Optionally save raw HTML to disk
                if self.extract:
                    self._save_page(item,
                                    raw_content if isinstance(raw_content, bytes)
                                    else raw_content.encode('utf-8'))

                # Parse HTML — lxml je C parser (5–10× rychlejší než html.parser),
                # BS4 zůstává jako rozhraní pro traversal a selektory.
                try:
                    soup = BeautifulSoup(html_content, features="lxml")
                except TypeError:
                    print(f"## Soup Error: couldn't parse {item}")
                    continue

                self.titles[item] = (
                    soup.title.string.strip()
                    if soup.title and soup.title.string else None
                )

                # Extract all navigable links from this page
                new_links = self._extract_links(soup, html_content, item)

                # Route: same base domain → inner queue; other .onion → outer queue
                for link in new_links:
                    if link not in ord_lst:
                        ord_lst.append(link)

                    link_base = clean_domain(link)

                    if link_base == current_base:
                        self._add_to_inner_queue(link, inner_queue, queued_inner, visited)
                    elif (link not in visited
                          and link_base not in queued_domains
                          and link_base not in pending_external):
                        pending_external[link_base] = link

                if inner_queue and float(self.c_pause) > 0:
                    time.sleep(float(self.c_pause))

            # ── Domain finished ────────────────────────────────────────────────
            if pages_in_domain > 0:
                domains_crawled += 1
                self.crawled_domains.append(seed_url)
                print(f"## Domain {current_base} done: {pages_in_domain} page(s) downloaded.")

            # Promote newly discovered external .onion domains to outer queue
            for ext_base, ext_url in pending_external.items():
                self._add_to_outer_queue(ext_url, domain_queue, queued_domains, visited)

            if self.verbose and pending_external:
                print(f"## Added {len(pending_external)} new domain(s) to queue. "
                      f"({len(domain_queue)} total pending)")

        self.pending_domains = list(domain_queue)
        stop_reason = " (stopped by user)" if self.stop_requested.is_set() else ""
        print(
            f"## Crawl completed{stop_reason}: {domains_crawled} domain(s) crawled, "
            f"{len(ord_lst)} link(s) found."
            f"{f' {len(self.pending_domains)} domain(s) pending.' if self.pending_domains else ''}"
        )
        return ord_lst

    # ── Helpers ────────────────────────────────────────────────────────────────

    def _is_image_link(self, link):
        """Return True if the URL path ends with a known image extension."""
        try:
            path = urlparse(link).path.lower()
        except Exception:
            path = str(link).lower()
        base = path.split('?', 1)[0].split('#', 1)[0]
        return any(base.endswith(ext) for ext in IMAGE_EXTS)

    def _serialized_findings(self):
        """Return findings as a JSON-serializable dict."""
        return {
            "start_url":      self.website,
            "links":          sorted(self.findings["links"]),
            "external_links": sorted(self.findings["external_links"]),
            "images":         sorted(self.findings["images"]),
            "scripts":        sorted(self.findings["scripts"]),
            "telephones":     sorted(self.findings["telephones"]),
            "emails":         sorted(self.findings["emails"]),
            "files":          sorted(self.findings["files"]),
        }

    def export_payload(self):
        """Return data needed for downstream exporters and the visualizer."""
        return {
            "start_url":       self.website,
            "data":            self._serialized_findings(),
            "edges":           set(self.edges),
            "titles":          dict(self.titles),
            "resources": {
                cat: {src: sorted(vals) for src, vals in sources.items()}
                for cat, sources in self.resources.items()
            },
            "crawled_domains": list(self.crawled_domains),
            "pending_domains": list(self.pending_domains),
        }
