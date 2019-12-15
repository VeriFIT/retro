#!/usr/bin/env python3
# Processes a file with a list of string equations into many files, each with a
# single equation

import sys

PREFIX = "eq"
SUFFIX = "txt"


###########################################
def save_to_file(lines, filename):
    """save_to_file(lines, filename)

    Saves a list of lines to a file with filename.
    """
    f = open(filename, "w+")
    f.writelines(lines, )

    f.close()
    return


###########################################
def dump_eq(lines, name_chunk):
    """dump_eq(lines, name_chunk)

    Dumps a list of lines into a file named according to the template.
    """
    return save_to_file(lines, PREFIX + str(name_chunk) + "." + SUFFIX)


###########################################
def proc_stream(fd):
    """proc_stream(fd) -> _|_

    Processes the input stream.
    """
    i = 0
    buffer = list()
    while True:
        line = fd.readline()
        if not line:
            break

        line = line.strip()
        # if not line:
        #     continue

        if line == "from:":
            continue

        if line == "":
            if len(buffer) > 0:
                dump_eq(buffer, i)
                buffer = list()
                i += 1
        elif line == "[Check SAT]":
            if i != 0:   # not the first
                dump_eq(buffer, i)
                buffer = list()
            i += 1
        else:
            buffer.append(line + "\n")

    if len(buffer) > 0:
        dump_eq(buffer, i)
    return


###############################
if __name__ == '__main__':
    argc = len(sys.argv)
    if argc == 1:
        fd = sys.stdin
    elif argc == 2:
        fd = open(sys.argv[1], "r")
    else:
        print("Invalid number of arguments: either 0 or 1 required")
        sys.exit(1)

    proc_stream(fd)
    if argc == 2:
        fd.close()
