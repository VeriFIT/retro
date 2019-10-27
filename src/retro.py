#!/usr/bin/env python3
#
# TODO: some blah blah

import sys

from RRTParser import parse_rrt

###########################################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc == 1:
        fd = sys.stdin
    elif argc == 2:
        fd = open(sys.argv[1], "r")
    else:
        print("Invalid number of arguments: either 0 or 1 required")
        sys.exit(1)

    aut = parse_rrt(fd)
    print(aut)

    if argc == 2:
        fd.close()
