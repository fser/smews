#!/usr/bin/python


import sys
import time
import sha
import random

from multiprocessing import Process
from urllib2 import urlopen

def get_page(url):
    f = urlopen(url)
    content = ''.join(f.readlines())

    if content.find('</html>'):
        OK = "OK"
    else:
        OK = "KO"

    filename = "output/" + sha.new(str(time.time() + random.random())).hexdigest() + ".html"
    

    with open('trace', 'a') as f:
        f.write("%s -> %s %s\n" % (time.ctime(), filename, OK))

    with open(filename, 'w') as f:
        f.write(content)

def multi_get_page(url, n):
    processes = []

    # create
    for i in xrange(n):
        print "create %d" % i
        processes.append(Process(target=get_page, args=(url,)))

    # start
    for p in processes:
        print "start a process"
        p.start()


if __name__ == '__main__':
    url = sys.argv[1]
    n = int(sys.argv[2])

    with open('trace', 'a') as f:
        f.write("Launching %d get_page @ %s\n" % (n, time.ctime()))

    multi_get_page(url, n)
