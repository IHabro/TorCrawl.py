#!/usr/bin/python
"""
TorCrawl.py is a python script to crawl and extract (regular or onion)
webpages through TOR network.

usage: python torcrawl.py [options]
python torcrawl.py -u l0r3m1p5umD0lorS1t4m3t.onion
python torcrawl.py -v -w -u http://www.github.com -o github.htm
python torcrawl.py -v -u l0r3m1p5umD0lorS1t4m3t.onion -c -d 2 -p 5
python torcrawl.py -v -w -u http://www.github.com -c -d 2 -p 5 -e -f GitHub

General:
-h, --help         : Help
-v, --verbose      : Show more information about the progress
-u, --url *.onion  : URL of Webpage to crawl or extract
-w, --without      : Without the use of Relay TOR
-wh, --whonix      : Use Whonix's built in proxy Gateway
-rua, --random-ua  : Enable random user-agent rotation for requests
-rpr, --random-proxy: Enable random proxy rotation from res/proxies.txt
-px, --proxy       : IP address for SOCKS5 proxy
-pr, --proxyport   : Port for SOCKS5 proxy
-V, --version      : Show version and exit

Crawl:
-c, --crawl       : Crawl website (Default output on /links.txt)
-e, --extract     : Save raw HTML to disk during crawl
-i, --input       : Input file with URL(s) (separated by line)
-p, --pause       : The length of time the crawler will pause (Default: 0)
-f, --folder      : Override the auto-generated output directory name
-j, --json        : Export crawl findings to JSON
-x, --xml         : Export crawl findings to XML
-DB, --database   : Export crawl findings and link graph to SQLite database
-vis, --visualization: Generate HTML visualization (requires -DB)
-l, --log         : Log file with visited URLs and their response code.
-mp, --maximum_pages   : Maximum number of pages per domain (Default: 10)
-md, --maximum_domains : Maximum number of domains to crawl (Default: 10)

GitHub: github.com/MikeMeliz/TorCrawl.py
License: GNU General Public License v3.0

"""

import argparse
import os
import socket
import sys
import datetime
import threading
import time

import socks  # noqa - pysocks

from modules.checker import check_ip
from modules.checker import check_tor
from modules.checker import url_canon
from modules.crawler import Crawler
from modules.export import export_json, export_xml, export_database
from modules.visualization import export_visualization

__version__ = "1.35"


def connect_tor(proxy_url, proxy_port):
    """ Connect to TOR via DNS resolution through a socket.

    :return: None or HTTPError.
    """
    try:
        socks.setdefaultproxy(socks.PROXY_TYPE_SOCKS5, proxy_url, proxy_port)
        socket.socket = socks.socksocket

        def getaddrinfo(*args):  # noqa
            return [(socket.AF_INET, socket.SOCK_STREAM, 6, '',
                     (args[0], args[1]))]

        socket.getaddrinfo = getaddrinfo  # noqa
    except socks.HTTPError as err:
        error = sys.exc_info()[0]
        print(f"Error: {error} \n## Cannot establish connection with TOR\n"
              f"HTTPError: {err}")


def build_output_path(base_dir='output'):
    """Create and return an auto-named crawl output folder inside *base_dir*.

    Folder name format:  Crawl_<DayAbbr><N>_<YYMMDD>
    Examples:            Crawl_Ne1_260315   (first crawl on a Sunday)
                         Crawl_Ne2_260315   (second crawl the same day)

    Day abbreviations (Czech): Po Út St Čt Pá So Ne
    N is determined automatically by counting existing folders for today.

    :param base_dir: String - root directory that will contain the crawl folder.
    :return: String - full path to the newly created crawl folder.
    """
    now = datetime.datetime.now()
    date_str = now.strftime("%y%m%d")
    days_cz = ['Po', 'Út', 'St', 'Čt', 'Pá', 'So', 'Ne']
    day_abbr = days_cz[now.weekday()]   # Monday = 0, Sunday = 6

    os.makedirs(base_dir, exist_ok=True)

    # Count existing same-day crawl folders to derive the next sequential N
    prefix = f"Crawl_{day_abbr}"
    suffix = f"_{date_str}"
    try:
        existing = [
            d for d in os.listdir(base_dir)
            if os.path.isdir(os.path.join(base_dir, d))
            and d.startswith(prefix) and d.endswith(suffix)
        ]
    except OSError:
        existing = []

    n = len(existing) + 1
    folder_name = f"Crawl_{day_abbr}{n}_{date_str}"

    # ./output/Crawl_DDN_YYMMDD
    full_path = os.path.join(base_dir, folder_name)
    os.makedirs(full_path, exist_ok=True)
    return full_path


def _keylistener_thread(stop_event):
    """Background thread that waits for Ctrl+S and sets *stop_event*.

    The thread puts the terminal into a mode where:
      - Characters arrive one at a time (no line buffering).
      - XON/XOFF flow control is disabled so Ctrl+S reaches this code
        instead of being swallowed by the OS as a pause signal.
      - Signals (ISIG) remain enabled, so Ctrl+C still raises SIGINT normally.
      - Terminal settings are always restored on exit (try/finally).

    On Windows the msvcrt module is used instead.
    When stdin is not a real TTY (e.g. piped input, CI) the function returns
    immediately without error.

    :param stop_event: threading.Event — set when Ctrl+S is detected.
    """
    try:
        if sys.platform == 'win32':
            import msvcrt
            while not stop_event.is_set():
                if msvcrt.kbhit():
                    ch = msvcrt.getwch()
                    if ch == '\x13':    # Ctrl+S
                        print("\n## Ctrl+S — stopping crawler after current page...")
                        stop_event.set()
                        break
                time.sleep(0.05)
        else:
            import termios
            fd = sys.stdin.fileno()
            if not os.isatty(fd):
                return  # Not a real terminal — nothing to listen on

            old_attrs = termios.tcgetattr(fd)
            try:
                new_attrs = termios.tcgetattr(fd)
                # c_iflag  — disable XON/XOFF so Ctrl+S is not swallowed
                new_attrs[0] &= ~termios.IXON
                # c_lflag  — disable line buffering and echo; keep ISIG so
                #            Ctrl+C continues to raise SIGINT
                new_attrs[3] &= ~(termios.ICANON | termios.ECHO)
                # c_cc     — return after every single byte, no timeout
                new_attrs[6][termios.VMIN]  = 1
                new_attrs[6][termios.VTIME] = 0
                termios.tcsetattr(fd, termios.TCSANOW, new_attrs)

                while not stop_event.is_set():
                    ch = os.read(fd, 1)
                    if ch == b'\x13':   # Ctrl+S
                        print("\n## Ctrl+S — stopping crawler after current page...")
                        stop_event.set()
                        break
            finally:
                # Always restore original terminal settings
                termios.tcsetattr(fd, termios.TCSADRAIN, old_attrs)
    except Exception:
        pass    # Non-TTY, permission error, or unsupported platform — skip silently


def _start_keylistener(stop_event):
    """Start *_keylistener_thread* as a daemon thread and return it.

    Daemon threads are killed automatically when the main thread exits,
    so there is no need to join this thread explicitly.

    :param stop_event: threading.Event — passed through to the listener thread.
    :return: threading.Thread
    """
    t = threading.Thread(
        target=_keylistener_thread,
        args=(stop_event,),
        daemon=True,
        name="keylistener",
    )
    t.start()
    return t


def main():
    """ Main method of TorCrawl application.

    :return: None
    """
    parser = argparse.ArgumentParser(
        description="TorCrawl.py is a python script to crawl and extract "
                    "(regular or onion) webpages through TOR network.")

    # General
    parser.add_argument('-v', '--verbose', action='store_true', help='Show more information about the progress')
    parser.add_argument('-u', '--url', help='URL of webpage to crawl or extract')
    parser.add_argument('-w', '--without', action='store_true', help='Without the use of Relay TOR')
    parser.add_argument('-wh', '--whonix', action='store_true', help='Run crawler inside Whonix (skip Tor connectivity check)')
    parser.add_argument('-V', '--version', action='version', version=f"%(prog)s {__version__}")

    # Crawl
    parser.add_argument('-c', '--crawl', action='store_true', help='Crawl website (Default output on /links.txt)')
    parser.add_argument('-e', '--extract', action='store_true', help='Save raw HTML pages to disk during crawl')
    parser.add_argument('-i', '--input', help='Input file with URL(s) (separated by line)')
    parser.add_argument('-p', '--pause', help='The length of time the crawler will pause')
    parser.add_argument('-l', '--log', action='store_true', help='Log visited URLs and their response codes')
    parser.add_argument('-f', '--folder', help='Override the auto-generated output directory name')
    parser.add_argument('-j', '--json', dest='json_export', action='store_true', help='Export crawl findings to JSON')
    parser.add_argument('-x', '--xml', dest='xml_export', action='store_true', help='Export crawl findings to XML')
    parser.add_argument('-DB', '--database', dest='database_export', action='store_true', help='Export crawl findings and link graph to SQLite database')
    parser.add_argument('-vis', '--visualization', dest='visualization', action='store_true', help='Generate HTML visualization from SQLite database (requires -DB)')
    parser.add_argument('-rua', '--random-ua', action='store_true', help='Enable random user-agent rotation for requests')
    parser.add_argument('-rpr', '--random-proxy', action='store_true', help='Enable random proxy rotation from res/proxies.txt')
    parser.add_argument('-pr', '--proxyport', help='Port for SOCKS5 proxy', default=9050)
    parser.add_argument('-px', '--proxy', help='IP address for SOCKS5 proxy', default='127.0.0.1')
    parser.add_argument('-md', '--maximum_domains', type=int, default=10, help='Maximum number of domains to crawl (default: 10)')
    parser.add_argument('-mp', '--maximum_pages', type=int, default=10, help='Maximum number of pages per domain (default: 10)')

    args = parser.parse_args()

    now = datetime.datetime.now().strftime("%y%m%d")
    results_prefix = f"{now}_results"

    # ── Resolve website URL and output folder ──────────────────────────────────

    website = ''
    output_folder = ''
    seed_urls = []
    url_arg = args.url.strip() if args.url else ''

    if args.input:
        try:
            with open(args.input, 'r', encoding='UTF-8') as f:
                seed_urls = [line.strip() for line in f
                             if line.strip() and not line.startswith('#')]
        except IOError as err:
            print(f"## ERROR reading input file {args.input}: {err}")
            sys.exit(2)

        if not seed_urls:
            print(f"## ERROR: Input file {args.input} contains no valid URLs.")
            sys.exit(2)

        website = url_canon(seed_urls[0], args.verbose)
        if args.verbose:
            print(f"## Loaded {len(seed_urls)} seed URL(s) from {args.input}")

        output_folder = (os.path.join('output', args.folder)
                         if args.folder else build_output_path())

    elif len(url_arg) > 0:
        website = url_canon(url_arg, args.verbose)
        output_folder = (os.path.join('output', args.folder)
                         if args.folder else build_output_path())
    else:
        print("## ERROR: URL is required unless --input is provided.")
        sys.exit(2)

    # Create output folder when a manual name was given (build_output_path creates it already)
    if args.folder:
        os.makedirs(output_folder, exist_ok=True)

    # ── Validate flags ─────────────────────────────────────────────────────────

    if args.visualization and not args.database_export:
        print("## Visualization requires --database (-DB) to generate the SQLite file.")
        sys.exit(2)

    random_ua = args.random_ua
    random_proxy = args.random_proxy

    if random_proxy and not args.without:
        print("## Warning: Random proxy rotation requires --without (-w) flag to disable TOR.")
        print("## Random proxy rotation disabled. Using TOR instead.")
        random_proxy = False

    # ── Connect to TOR / proxy ─────────────────────────────────────────────────

    if random_proxy:
        if args.verbose:
            print("## Random proxy rotation enabled (TOR disabled)")
    elif args.whonix:
        if args.verbose:
            print("## Whonix mode: TOR is handled transparently by the OS, skipping setup")
    elif not args.without:
        check_tor(args.verbose)
        connect_tor(args.proxy, args.proxyport)

    if args.verbose:
        check_ip()
        if args.url:
            print(f"## URL: {args.url}")

    # ── Crawl ──────────────────────────────────────────────────────────────────

    pause = args.pause if args.pause else 0
    input_file = args.input if args.input else ''

    crawler = Crawler(
        website, pause, output_folder, args.log, args.verbose,
        random_ua, random_proxy,
        max_domains=args.maximum_domains,
        max_pages=args.maximum_pages,
        extract=args.extract,
        seed_urls=seed_urls,
    )

    # Start the Ctrl+S listener — shares the crawler's own stop_requested event
    # so pressing Ctrl+S during crawl sets the flag the inner/outer loops check.
    print("## Press Ctrl+S at any time to stop crawling and save results.")
    _start_keylistener(crawler.stop_requested)

    try:
        lst = crawler.crawl()
    except Exception as e:
        print("!! Unexpected Crawler error, terminating crawling and saving data")
        print(f"!! Error: {e}")
        pass

    # Signal the keylistener to exit cleanly (it is a daemon so it would die
    # anyway, but setting the event lets it skip its final termios restore
    # wait and return immediately).
    crawler.stop_requested.set()

    # Write discovered links to file
    if not input_file:
        input_file = os.path.join(output_folder, 'links.txt')

    with open(input_file, 'w+', encoding='UTF-8') as f:
        for item in lst:
            f.write(f"{item}\n")
    print(f"## File created on {os.getcwd()}/{input_file}")

    # ── Export results ─────────────────────────────────────────────────────────

    payload = crawler.export_payload()

    crawled_path = os.path.join(output_folder, 'crawled_domains.txt')
    with open(crawled_path, 'w+', encoding='UTF-8') as f:
        for url in payload["crawled_domains"]:
            f.write(url + '\n')
    print(f"## Crawled domains: {crawled_path} ({len(payload['crawled_domains'])} domain(s))")

    if payload["pending_domains"]:
        pending_path = os.path.join(output_folder, 'pending_domains.txt')
        with open(pending_path, 'w+', encoding='UTF-8') as f:
            for url in payload["pending_domains"]:
                f.write(url + '\n')
        print(f"## Pending domains: {pending_path} ({len(payload['pending_domains'])} domain(s))")
        print(f"## Resume with: python torcrawl.py -c -e -i {pending_path}")

    if args.json_export:
        export_json(output_folder, results_prefix, payload["data"], verbose=args.verbose)
    if args.xml_export:
        export_xml(output_folder, results_prefix, payload["data"], verbose=args.verbose)
    if args.database_export:
        export_database(output_folder, results_prefix, payload["data"],
                        payload["edges"], payload["titles"], payload["resources"],
                        verbose=args.verbose)
    if args.visualization:
        export_visualization(output_folder, results_prefix, payload["start_url"],
                             verbose=args.verbose)


if __name__ == "__main__":
    main()
