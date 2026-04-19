#!/usr/bin/python

# Originally from TorCrawl.py by MikeMeliz (https://github.com/MikeMeliz/TorCrawl.py)
# Modified by Vojtěch Habrnal, 2025–2026, as part of diploma thesis
# Licensed under GNU GPLv3

import os
import importlib.resources as resources
import random
import re
import socket
import ssl
import subprocess
import sys
import urllib.request
from json import load
from urllib.error import HTTPError
from urllib.parse import urlparse
from urllib.request import urlopen


def url_canon(website, verbose):
    """ URL normalisation/canonicalization

    :param website: String - URL of website.
    :param verbose: Boolean - Verbose logging switch.
    :return: String 'website' - normalised result.
    """
    if not website.startswith("http://") and not website.startswith("https://"):
        website = "https://" + website
        if verbose:
            print(("## URL fixed: " + website))
    return website


def strip_www(netloc):
    """ Strips leading 'www.' from a netloc string.

    :param netloc: String - Hostname, e.g. 'www.example.onion'
    :return: String - Bare domain, e.g. 'example.onion'
    """
    return netloc[4:] if netloc.startswith("www.") else netloc


def make_request(url, random_ua=False, random_proxy=False, timeout=10, ssl_ctx=None):
    """ Makes an HTTP request with optional random user-agent, proxy and SSL context.
    Centralises the shared request logic used by the crawler.

    :param url: String - URL to request.
    :param random_ua: Boolean - Whether to use random user-agent rotation.
    :param random_proxy: Boolean - Whether to use random proxy rotation.
    :param timeout: Integer - Request timeout in seconds.
    :param ssl_ctx: ssl.SSLContext or None - Optional SSL context.
    :return: HTTPResponse object.
    """
    if random_proxy:
        proxy = get_random_proxy()
        if proxy:
            setup_proxy_connection(proxy)

    kwargs = {'timeout': timeout}
    if ssl_ctx is not None:
        kwargs['context'] = ssl_ctx

    if random_ua:
        user_agent = get_random_user_agent()
        if user_agent:
            req = urllib.request.Request(url, headers={'User-Agent': user_agent})
            return urllib.request.urlopen(req, **kwargs)

    return urllib.request.urlopen(url, **kwargs)


def check_tor(verbose):
    """Checks to see if TOR service is running on device.
    Will exit if (-w) with argument is provided on application startup and TOR
    service is not found to be running on the device.

    :param verbose: Boolean -'verbose' logging argument.
    :return: None
    """
    check_for_tor = subprocess.check_output(['ps', '-e'])

    def find_whole_word(word):
        return re.compile(r'\b({0})\b'.format(word),
                          flags=re.IGNORECASE).search

    if find_whole_word('tor')(str(check_for_tor)):
        if verbose:
            print("## TOR is ready!")
    else:
        print("## TOR is NOT running!")
        print('## Enable tor with \'service tor start\' or add -w argument')
        sys.exit(2)


def check_ip():
    """ Checks users IP from external resource.
    :return: None or HTTPError
    """
    api_address = 'https://api.ipify.org/?format=json'
    try:
        my_ip = load(urlopen(api_address))['ip']
        print(f'## Your IP: {my_ip}')
    except HTTPError as err:
        error = sys.exc_info()[0]
        print(f"Error: {error} \n## IP cannot be obtained. \n## Is {api_address} up? "
              f"\n## HTTPError: {err}")


_user_agents_cache = None
_proxies_cache = None


def _read_resource_file(filename):
    """Return absolute path to packaged resource, falling back to CWD."""
    try:
        return resources.files("res").joinpath(filename)
    except (FileNotFoundError, ModuleNotFoundError):
        return os.path.join("res", filename)


def get_random_user_agent():
    """ Loads user-agents from res/user_agents.txt and returns a random one.

    :return: String - Random user-agent string
    """
    global _user_agents_cache

    if _user_agents_cache is None:
        user_agents_file = _read_resource_file('user_agents.txt')
        try:
            with open(user_agents_file, 'r', encoding='UTF-8') as f:
                _user_agents_cache = [
                    line.strip()
                    for line in f
                    if line.strip() and not line.strip().startswith('#')
                ]
        except IOError:
            print(f"## Warning: Could not load user-agents from {user_agents_file}")
            return None

    if _user_agents_cache:
        return random.choice(_user_agents_cache)
    return None


def get_random_proxy():
    """ Loads proxies from res/proxies.txt and returns a random one.
    If no proxies are found, displays a helpful message with instructions.

    :return: String - Random proxy string (format: host:port) or None
    """
    global _proxies_cache

    if _proxies_cache is None:
        proxies_file = _read_resource_file('proxies.txt')
        try:
            with open(proxies_file, 'r', encoding='UTF-8') as f:
                _proxies_cache = [
                    line.strip()
                    for line in f
                    if line.strip() and not line.strip().startswith('#')
                ]
        except IOError:
            print(f"## Warning: Could not load proxies from {proxies_file}")
            return None

        if not _proxies_cache:
            print("## No proxies found in res/proxies.txt")
            print("## Please add proxies to res/proxies.txt, one per line.")
            print("## Example format:")
            print("##   127.0.0.1:9050")
            print("##   192.168.1.1:8080")
            print("##   proxy.example.com:3128")
            return None

    if _proxies_cache:
        return random.choice(_proxies_cache)
    return None


def setup_proxy_connection(proxy_string):
    """ Sets up a SOCKS5 proxy connection for a request.

    :param proxy_string: String - Proxy in format "host:port"
    :return: None
    """
    try:
        import socks  # noqa - pysocks
    except ImportError:
        print("## Error: pysocks module is required for proxy rotation. "
              "Install it with: pip install pysocks")
        return

    try:
        if ':' not in proxy_string:
            print(f"## Warning: Invalid proxy format: {proxy_string}. Expected host:port")
            return

        proxy_host, proxy_port = proxy_string.split(':', 1)
        proxy_port = int(proxy_port)

        socks.setdefaultproxy(socks.PROXY_TYPE_SOCKS5, proxy_host, proxy_port)
        socket.socket = socks.socksocket

        def getaddrinfo(*args):  # noqa
            return [(socket.AF_INET, socket.SOCK_STREAM, 6, '',
                     (args[0], args[1]))]

        socket.getaddrinfo = getaddrinfo  # noqa
    except (ValueError, socks.HTTPError) as err:
        print(f"## Warning: Could not set up proxy {proxy_string}: {err}")
