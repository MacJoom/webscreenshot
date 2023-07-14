#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# This file is part of webscreenshot.
#
# Copyright (C) 2020, Thomas Debize <tdebize at mail.com>
# All rights reserved.
#
# webscreenshot is free software: you can redistribute it and/or modify
# it under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# webscreenshot is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with webscreenshot.  If not, see <http://www.gnu.org/licenses/>.

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function
from flask import Flask, request, send_from_directory
from flask_httpauth import HTTPTokenAuth

import re
import os
import sys
import subprocess
import datetime
import time
import signal
import multiprocessing
import itertools
import shlex
import logging
import errno
import base64
import io

# Options definition
class Options:
    input_file = None
    URL = "wdm-zh.ch"
    verbosity = 0
    log_level = 2
    timeout = 30
    no_xserver = True
    ssl = False
    port = None
    multiprotocol = False
    renderer = "chromium"
    renderer_binary = None
    single_output_file = None
    output_directory = None
    workers = 4
    window_size = "1200,900"
    scale_factor = "0.5"
    proxy = None
    label = False
    no_error_file = False

# Python 2 and 3 compatibility
if (sys.version_info < (3, 0)):
    os_getcwd = os.getcwdu
    izip = itertools.izip
    
else:
    os_getcwd = os.getcwd
    izip = zip

# Script version
VERSION = '2.94'


# renderer binaries, hoping to find it in a $PATH directory
## Be free to change them to your own full-path location 
PHANTOMJS_BIN = 'phantomjs'
CHROME_BIN = 'google-chrome'
CHROMIUM_BIN = 'chromium'
FIREFOX_BIN = 'firefox'
XVFB_BIN = "xvfb-run -a"
IMAGEMAGICK_BIN = "convert"

WEBSCREENSHOT_JS = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), './webscreenshot.js'))
SCREENSHOTS_DIRECTORY = os.path.abspath(os.path.join(os_getcwd(), './screenshots/'))
FAILED_SCREENSHOTS_FILE = os.path.abspath(os.path.join(os_getcwd(), './webscreenshots_failed.txt'))

# Logger definition
LOGLEVELS = {0 : 'ERROR', 1 : 'INFO', 2 : 'DEBUG'}
logger_output = logging.StreamHandler(sys.stdout)
logger_output.setFormatter(logging.Formatter('[%(levelname)s][%(name)s] %(message)s'))

logger_gen = logging.getLogger("General")
logger_gen.addHandler(logger_output)

# Macros
SHELL_EXECUTION_OK = 0
SHELL_EXECUTION_ERROR = -1
PHANTOMJS_HTTP_AUTH_ERROR_CODE = 2

CONTEXT_RENDERER = 'renderer'
CONTEXT_IMAGEMAGICK = 'imagemagick'

# Handful patterns
p_ipv4_elementary = r'(?:[\d]{1,3})\.(?:[\d]{1,3})\.(?:[\d]{1,3})\.(?:[\d]{1,3})'
p_domain = r'[a-z0-9]+([\-\.]{1}[a-z0-9]+)*\.[a-z]+'
p_port = r'\d{0,5}'
p_resource = r'(?:/(?P<res>.*))?'

full_uri_domain = re.compile(r'^(?P<protocol>http(?:|s))://(?P<host>%s|%s)(?::(?P<port>%s))?%s$' % (p_domain, p_ipv4_elementary, p_port, p_resource))

fqdn_and_port = re.compile(r'^(?P<host>%s):(?P<port>%s)%s$' % (p_domain, p_port, p_resource))
fqdn_only = re.compile(r'^(?P<host>%s)%s$' % (p_domain, p_resource))

ipv4_and_port = re.compile(r'^(?P<host>%s):(?P<port>%s)%s' % (p_ipv4_elementary, p_port, p_resource))
ipv4_only = re.compile(r'^(?P<host>%s)%s$' % (p_ipv4_elementary, p_resource))

entry_from_csv = re.compile(r'^(?P<host>%s|%s)\s+(?P<port>\d+)$' % (p_domain, p_ipv4_elementary))

# Handful functions
def is_windows():
    """
        Are we running on Windows or not ?
    """
    return "win32" in sys.platform.lower()

def init_worker():
    """ 
        Tell the workers to ignore a global SIGINT interruption
    """
    signal.signal(signal.SIGINT, signal.SIG_IGN)

def kill_em_all(sig, frame):
    """
        Terminate all processes while capturing a SIGINT from the user
    """
    logger_gen.info('CTRL-C received, exiting')
    if is_windows():
        multiprocessing.sys.exit(1)
    
    else:
        pid = os.getpid()
        pgid = os.getpgid(pid)
        sid = os.getsid(os.getpid())
        
        # if launched with --no-xserver
        if pid == sid:
            os.killpg(pgid, signal.SIGKILL)
        else:
            time.sleep(4)
            multiprocessing.sys.exit(1)

def shell_exec(url, command, options, context):
    """
        Execute a shell command following a timeout
        Taken from http://howto.pui.ch/post/37471155682/set-timeout-for-a-shell-command-in-python
    """
    global SHELL_EXECUTION_OK, SHELL_EXECUTION_ERROR
    
    logger_url = logging.getLogger("%s" % url)
    logger_url.setLevel(options.log_level)
    
    timeout = int(options.timeout)
    start = datetime.datetime.now()
    
    def group_subprocesses():
        if options.no_xserver and not(is_windows()):
            os.setsid()
    
    def close_subfds(s):
        s.stdout.close()
        s.stderr.close()
    
    try :
        if is_windows():
            p = subprocess.Popen(shlex.split(command, posix=not(is_windows())), shell=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        else:
            p = subprocess.Popen(shlex.split(command, posix=not(is_windows())), shell=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=group_subprocesses)
        
        # binaries timeout
        while p.poll() is None:
            time.sleep(0.1)
            now = datetime.datetime.now()
            if (now - start).seconds > timeout:
                logger_url.debug("Shell command PID %s reached the timeout, killing it now" % p.pid)
                logger_url.error("Screenshot somehow failed\n")
                
                close_subfds(p)
                
                if is_windows():
                    p.send_signal(signal.SIGTERM)
                else:
                    if options.no_xserver:
                        pgid = os.getpgid(p.pid)
                        os.killpg(pgid, signal.SIGKILL)
                    else:
                        p.send_signal(signal.SIGKILL)
                
                return SHELL_EXECUTION_ERROR
        
        retval = p.poll()
        close_subfds(p)
        
        if retval != SHELL_EXECUTION_OK:
            if retval == PHANTOMJS_HTTP_AUTH_ERROR_CODE:
                # HTTP Authentication request
                logger_url.error("HTTP Authentication requested, try to pass credentials with -u and -b options")
            else:
                # Phantomjs general error
                logger_url.error("Shell command PID %s returned an abnormal error code: '%s'" % (p.pid,retval))
                logger_url.error("Screenshot somehow failed\n")
                    
            return SHELL_EXECUTION_ERROR
        
        else:
            logger_url.debug("Shell command PID %s ended normally" % p.pid)
            logger_url.info("Screenshot OK\n")
            return SHELL_EXECUTION_OK
    
    except OSError as e:
        if e.errno and e.errno == errno.ENOENT :
            default_message = '%s binary could not have been found in your current PATH environment variable, exiting' % context
            
            if context == CONTEXT_RENDERER:
                if options.no_xserver and not is_windows():
                    logger_url.error('No X server has been found and the xvfb-run binary could not be found, please install xvfb on your system')
                else:
                    logger_url.error(default_message)
            
            elif context == CONTEXT_IMAGEMAGICK:
                logger_url.error(default_message)
            
            return SHELL_EXECUTION_ERROR
        
    except Exception as err:
        logger_gen.error('Unknown error: %s, exiting' % err)
        return SHELL_EXECUTION_ERROR

def filter_bad_filename_chars_and_length(filename):
    """
        Filter bad chars for any filename
    """
    # Before, just avoid triple underscore escape for the classic '://' pattern, and length (max filename length is 255 on common OSes, but some renderer do not support that length while passing arguments for execution)
    filename = filename.replace('://', '_')[:129]
    
    return re.sub(r'[^\w\-_\. ]', '_', filename)

def extract_all_matched_named_groups(regex, match):
    """
        Return a set of all extractable matched parameters.
        >>> full_uri_domain.groupindex
        {'domain': 1, 'port': 3}
        >>>full_uri_domain.match('http://8.8.8.8:80').group('domain')
        '8.8.8.8'
        >>>extract_all_matched_named_groups() => {'domain': '8.8.8.8', 'port': '80'}
            
    """
    result = {}
    for name, id in regex.groupindex.items():
        matched_value = match.group(name)
        if matched_value != None: result[name] = matched_value
    
    return result

def entry_format_validator(line):
    """
        Validate the current line against several regexes and return matched parameters (ip, domain, port etc.)
    """
    tab = { 'full_uri_domain'       : full_uri_domain,
            'fqdn_only'             : fqdn_only,
            'fqdn_and_port'         : fqdn_and_port, 
            'ipv4_and_port'         : ipv4_and_port, 
            'ipv4_only'             : ipv4_only, 
            'entry_from_csv'        : entry_from_csv }
    
    for name, regex in tab.items():
        validator = regex.match(line)
        if validator:
            return extract_all_matched_named_groups(regex, validator)

def parse_targets(options):
    """
        Parse list and convert each target to valid URI with port(protocol://foobar:port) 
    """
    
    target_list = []
    
    if options.input_file != None:
        with open(options.input_file,'rb') as fd_input:
            try:
                lines = [l.decode('utf-8').strip() for l in fd_input.readlines()]
            
            except UnicodeDecodeError as e:
                logger_gen.error('Your input file is not UTF-8 encoded, please encode it before using this script')
                sys.exit(1)
    else:
        lines = [options.URL]
        
    for index, line in enumerate(lines, start=1):
        matches = entry_format_validator(line)
        
        # pass if line can be recognized as a correct input, or if no 'host' group could be found with all the regexes
        if matches == None or not('host' in matches.keys()):
            logger_gen.warning("Line %s '%s' could not have been recognized as a correct input" % (index, line))
            pass
        else:
            host = matches['host']
            
            # Protocol is 'http' by default, unless ssl is forced
            if options.ssl == True:
                protocol = 'https'
            elif 'protocol' in matches.keys():
                protocol = str(matches['protocol'])
            else:
                protocol = 'http'
            
            # Port is ('80' for http) or ('443' for https) by default, unless a specific port is supplied
            if options.port != None:
                port = options.port
            elif 'port' in matches.keys():
                port = int(matches['port'])
                
                # if port is 443 and no protocol has been found earlier, assume protocol is https
                if port == 443 and not('protocol' in matches.keys()):
                    protocol = 'https'
            else:
                port = 443 if protocol == 'https' else 80
            
            # No resource URI by default
            if 'res' in matches.keys():
                res = "/" + str(matches['res'])
            else:
                res = ''
            
            # perform screenshots over HTTP and HTTPS for each target
            if options.multiprotocol:
                final_uri_http_port = int(matches['port']) if 'port' in matches.keys() else 80
                final_uri_http = '%s://%s:%s%s' % ('http', host, final_uri_http_port, res)
                target_list.append(final_uri_http)
                logger_gen.info("'%s' has been formatted as '%s' with supplied overriding options" % (line, final_uri_http))
                
                
                final_uri_https_port = int(matches['port']) if 'port' in matches.keys() else 443
                final_uri_https = '%s://%s:%s%s' % ('https', host, final_uri_https_port, res)
                target_list.append(final_uri_https)
                logger_gen.info("'%s' has been formatted as '%s' with supplied overriding options" % (line, final_uri_https))
            
            else:
                final_uri = '%s://%s:%s%s' % (protocol, host, port, res)
                target_list.append(final_uri)

                logger_gen.info("'%s' has been formatted as '%s' with supplied overriding options" % (line, final_uri))
    
    return target_list

def craft_bin_path(options, context=CONTEXT_RENDERER):
    """
        Craft the proper binary path for renderer 
    """
    global PHANTOMJS_BIN, CHROME_BIN, CHROMIUM_BIN, FIREFOX_BIN, XVFB_BIN, IMAGEMAGICK_BIN
    
    final_bin = []
    
    if context == CONTEXT_RENDERER:
        if options.no_xserver:
            final_bin.append(XVFB_BIN)
        
        if options.renderer_binary != None: 
            final_bin.append(os.path.join(options.renderer_binary))
        
        else:
            if options.renderer == 'phantomjs':
                final_bin.append(PHANTOMJS_BIN)
            
            elif options.renderer == 'chrome':
                final_bin.append(CHROME_BIN)
            
            elif options.renderer == 'chromium':
                final_bin.append(CHROMIUM_BIN)
            
            elif options.renderer == 'firefox':
                final_bin.append(FIREFOX_BIN)
    
    elif context == CONTEXT_IMAGEMAGICK:
        if options.imagemagick_binary != None:
            final_bin.append(os.path.join(options.imagemagick_binary))
        
        else:
            final_bin.append(IMAGEMAGICK_BIN)
    
    return " ".join(final_bin)

def craft_arg(param):
    """
        Craft arguments with proper quotes
    """
    if is_windows():
        return '%s' % param
    else:
        return '"%s"' % param

def launch_cmd(logger, url, cmd_parameters, options, context):
    """
        Launch the actual command
    """
    cmd = " ".join(cmd_parameters)
    logger.debug("Shell command to be executed\n'%s'\n" % cmd)
    execution_retval = shell_exec(url, cmd, options, context)
    
    return execution_retval

def craft_output_filename_and_format(url, options):
    """
        Craft the output filename and format
    """
    output_format = options.format if options.renderer == 'phantomjs' else 'png'
    
    if options.single_output_file:
        if options.single_output_file.lower().endswith('.%s' % output_format):
            output_filename = os.path.abspath(filter_bad_filename_chars_and_length(options.single_output_file))
        else:
            output_filename = os.path.abspath(filter_bad_filename_chars_and_length('%s.%s' % (options.single_output_file, output_format)))
        
    else:
        output_filename = os.path.join(options.output_directory, ('%s.%s' % (filter_bad_filename_chars_and_length(url), output_format)))
    
    return output_format, output_filename

def craft_cmd(url_and_options):
    """
        Craft the correct command with url and options
    """
    global logger_output, WEBSCREENSHOT_JS, SHELL_EXECUTION_OK, SHELL_EXECUTION_ERROR
    
    url, options = url_and_options
    
    logger_url = logging.getLogger("%s" % url)
    logger_url.addHandler(logger_output)
    logger_url.setLevel(options.log_level)
    
    output_format, output_filename = craft_output_filename_and_format(url, options)
        
    # PhantomJS renderer
    if options.renderer == 'phantomjs':
        # If you ever want to add some voodoo options to the phantomjs command to be executed, that's here right below
        cmd_parameters = [ craft_bin_path(options),
                           '--ignore-ssl-errors=true',
                           '--ssl-protocol=any',
                           '--ssl-ciphers=ALL' ]
        
        cmd_parameters.append("--proxy %s" % options.proxy) if options.proxy != None else None
        cmd_parameters.append("--proxy-auth %s" % options.proxy_auth) if options.proxy_auth != None else None
        cmd_parameters.append("--proxy-type %s" % options.proxy_type) if options.proxy_type != None else None

        cmd_parameters.append('%s url_capture=%s output_file=%s' % (craft_arg(WEBSCREENSHOT_JS), url, craft_arg(output_filename)))
        
        cmd_parameters.append('header="Cookie: %s"' % options.cookie.rstrip(';')) if options.cookie != None else None
        
        if options.http_username != None:
            if options.http_password != None:
                basic_authentication_header = base64.b64encode(str("%s:%s" % (options.http_username, options.http_password)).encode()).decode()
            
            else:
                basic_authentication_header = base64.b64encode(str("%s:" % (options.http_username)).encode()).decode()
            
            cmd_parameters.append('header="Authorization: Basic %s"' % basic_authentication_header)
        
        width = options.window_size.split(',')[0]
        height = options.window_size.split(',')[1]
        
        cmd_parameters.append('width=%d' % int(width))
        cmd_parameters.append('height=%d' % int(height))
        
        cmd_parameters.append('format=%s' % options.format)
        cmd_parameters.append('quality=%d' % int(options.quality))
        
        cmd_parameters.append('ajaxtimeout=%d' % int(options.ajax_max_timeouts.split(',')[0]))
        cmd_parameters.append('maxtimeout=%d' % int(options.ajax_max_timeouts.split(',')[1]))
        
        if options.crop != None:
            crop_rectangle = options.crop.replace('w', width).replace('h', height)
            cmd_parameters.append('crop="%s"' % crop_rectangle)
        
        if options.header:
            for header in options.header:
                cmd_parameters.append('header="%s"' % header.rstrip(';'))
       
        if options.custom_js and os.path.exists(options.custom_js):
            cmd_parameters.append('customjs=%s' % craft_arg(os.path.abspath(options.custom_js)))
       
    
    # Chrome and chromium renderers
    elif (options.renderer == 'chrome') or (options.renderer == 'chromium') or (options.renderer == 'edgechromium'): 
        cmd_parameters =  [ craft_bin_path(options),
                            '--allow-running-insecure-content',
                            '--ignore-certificate-errors',
                            '--ignore-urlfetcher-cert-requests',
                            '--reduce-security-for-testing',
                            '--no-sandbox',
                            '--headless',
                            '--disable-gpu',
                            '--hide-scrollbars',
                            '--incognito' if (options.renderer == 'chrome') or (options.renderer == 'chromium') else '-inprivate',
                            '-screenshot=%s' % craft_arg(output_filename),
                            '--window-size=%s' % options.window_size,
                            '--force-device-scale-factor=%s' % options.scale_factor,
                            '%s' % craft_arg(url) ]
        cmd_parameters.append('--proxy-server=%s' % options.proxy) if options.proxy != None else None
    
    # Firefox renderer
    elif options.renderer == 'firefox': 
        cmd_parameters =  [ craft_bin_path(options),
                            '--new-instance',
                            '--screenshot=%s' % craft_arg(output_filename),
                            '--window-size=%s' % options.window_size,
                            '%s' % craft_arg(url) ]
                            
    execution_retval = launch_cmd(logger_url, url, cmd_parameters, options, CONTEXT_RENDERER)
    
    # ImageMagick URL embedding
    if options.label and execution_retval == SHELL_EXECUTION_OK:
        output_filename_label = os.path.join(options.output_directory, ('%s_with_label.%s' % (filter_bad_filename_chars_and_length(url), output_format)))
        cmd_parameters = [ craft_bin_path(options, 'imagemagick'),
                           craft_arg(output_filename),
                           '-pointsize %s' % options.label_size,
                           '-gravity Center',
                           '-background %s' % options.label_bg_color,
                           "label:'%s'" % url,
                           '+swap',
                           '-append %s' % craft_arg(output_filename_label) ]
        
        execution_retval_label = launch_cmd(logger_url, url, cmd_parameters, options, CONTEXT_IMAGEMAGICK)
    
    return execution_retval, url, output_filename

def take_screenshot(url_list, options, interactiv):
    """
        Launch the screenshot workers
        Thanks http://noswap.com/blog/python-multiprocessing-keyboardinterrupt
    """
    global SHELL_EXECUTION_OK, SHELL_EXECUTION_ERROR
    
    screenshot_number = len(url_list)

    if interactiv:
        print("[+] %s URLs to be screenshot" % screenshot_number)
    
    pool = multiprocessing.Pool(processes=int(options.workers), initializer=init_worker)
    
    taken_screenshots = [r for r in pool.imap(func=craft_cmd, iterable=izip(url_list, itertools.repeat(options)))]
    
    pool.close()
    pool.join()
    
    screenshots_error_url = [url for retval, url, output in taken_screenshots if retval == SHELL_EXECUTION_ERROR]
    screenshots_error = sum(retval == SHELL_EXECUTION_ERROR for retval, url, output in taken_screenshots)
    screenshots_ok = int(screenshot_number - screenshots_error)
    screenshots_output = [output for retval, url, output in taken_screenshots if retval == 0]

    if interactiv:
        print("[+] %s actual URLs screenshot" % screenshots_ok)
        print("[+] %s error(s)" % screenshots_error)
        for s in screenshots_output:
            print("Output Filename: %s" % s)

        if screenshots_error != 0:
            if not(options.no_error_file):
                with io.open(FAILED_SCREENSHOTS_FILE, 'w', newline='\n') as fd_out:
                    for url in screenshots_error_url:
                        fd_out.write(url + '\n')
                        print("    %s" % url)
            else:
                for url in screenshots_error_url:
                    print("    %s" % url)

    return screenshots_output


def prepare(options):
    global VERSION, SCREENSHOTS_DIRECTORY, LOGLEVELS
    options.log_level = LOGLEVELS[options.verbosity]
    logger_gen.setLevel(options.log_level)

    if options.single_output_file:
        options.workers = 1

    if options.output_directory != None:
        options.output_directory = os.path.join(os_getcwd(), options.output_directory)
    else:
        options.output_directory = SCREENSHOTS_DIRECTORY

    logger_gen.debug("Options: %s\n" % options)
    if not os.path.exists(options.output_directory):
        logger_gen.info("'%s' does not exist, will then be created" % options.output_directory)
        os.makedirs(options.output_directory)


def main():
    """
        Dat main
    """
    global VERSION, SCREENSHOTS_DIRECTORY, LOGLEVELS
    signal.signal(signal.SIGINT, kill_em_all)
    
    print('webscreenshot.py version %s\n' % VERSION)

    options = Options()

    prepare(options)

    url_list = parse_targets(options)

    print(url_list)    
    
    take_screenshot(url_list, options, True)
    
    return None

if __name__ == "__main__" :
    main()

app = Flask(__name__)
auth = HTTPTokenAuth(scheme='Bearer')

tokens = {
    "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCIsImtpZCI6Imd1MTVXQVpTY052US1qQ1NJZ1lUTSJ9.eyJpc3MiOiJodHRwczovL2Rldi1kbzVrN2MyZWc2MnBoNjR5LmV1LmF1dGgwLmNvbS8iLCJzdWIiOiJNQlFkc01JSXI2QmVZZTd6TWR3S0tjZDFVOWNwamk3RUBjbGllbnRzIiwiYXVkIjoid2Vic2NyZWVuc2hvdC5pbmZvdGVjaC5jaC9zY3JlZW5zaG90IiwiaWF0IjoxNjg4NjQzNTI5LCJleHAiOjE2OTEyMzU1MjksImF6cCI6Ik1CUWRzTUlJcjZCZVllN3pNZHdLS2NkMVU5Y3BqaTdFIiwiZ3R5IjoiY2xpZW50LWNyZWRlbnRpYWxzIn0.VspifLVrARSco3ZVqME6CAMPcSewmsvYyrZgY4fv81hFS6SXMrc1FHvu2M7bxpojrsXM5lGalOVabl5vQBapFkEJ7UQYxqS8LKnkaw81NNO37_G9_Ay-KhZkd0vw6CC3dMVBRZdm4TJiJWlEK5CL694tYhCWaTVBPhFy20-ISxs4T6wBHt7CcxSACZ8M7WuEhZDyiY8czwfd4eIEsNVgpGj6VfC39FPaD3_uO2d5vD7BRehwEh8cQniL5XI_EMJS9zpq8xUWeUoFyo5AcqBxRgTdNDBEMayqsymxdFthi4kBG9CpCNiPtSAXQt7WjxZYEnZMhnCXAdfFJHi6NQ_HFg": "webscreenshot",
}

@auth.verify_token
def verify_token(token):
    if token in tokens:
        return tokens[token]

@app.route("/screenshot", methods=['POST'])
@auth.login_required
def get_screenshot():
    global VERSION, SCREENSHOTS_DIRECTORY, LOGLEVELS

    options = Options()

    params = request.get_json()
    for p in params:
        setattr(options, p, params[p])

    prepare(options)

    url_list = parse_targets(options)

    screenshots = take_screenshot(url_list, options, False)

    for s in screenshots:
        p = os.path.split(s)
        return send_from_directory(p[0], p[1], as_attachment=True)
