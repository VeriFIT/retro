#!/usr/bin/env python3

"""
 Script for automated experimental evaluation.
 @title experimental.py
 @author Vojtech Havlena, November 2019
"""

import sys
import getopt
import subprocess
import string
import re
import os
import os.path
import resource

SATLINE = -2
TIMELINE = -1
MODEL_CHECK = -3
TIMEOUT = 10 #in seconds
FORMULAS = 1000

def main():
    #Input parsing
    if len(sys.argv) < 3:
        help_err()
        sys.exit()
    try:
        opts, args = getopt.getopt(sys.argv[3:], "tf:", ["tex", "formulas="])
    except getopt.GetoptError as err:
        help_err()
        sys.exit()

    bin = sys.argv[1]
    formulafolder = sys.argv[2]
    texout = False
    FORMULAS = 1000

    for o, a in opts:
        if o in ("-t", "--tex"):
            texout = True
        if o in ("-f", "--formulas"):
            FORMULAS = int(a)

    #Experiments

    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".smt2")]
    files.sort()
    files = files[:FORMULAS]
    tex = "Timeout: {0}\n".format(TIMEOUT)
    tex += "\\begin{table}[h]\n\\begin{tabular}{lll}\n"
    tex += "\\textbf{Formula File} & \\textbf{Time} & \\textbf{Sat} \\\\\n\\toprule \n"

    print_config(FORMULAS)
    print("Formula: time, sat")

    for eq_file in files:
        filename = os.path.join(formulafolder, eq_file)

        try:
            output = subprocess.check_output([bin, filename, "../automata/rrt-x-yx-len.vtf", "../automata/rrt-x-eps-len.vtf", "../automata/rrt-x-yx.vtf", "../automata/rrt-x-eps.vtf"], \
                timeout=TIMEOUT).decode("utf-8")
            rmc_parse = parse_output(output)
        except subprocess.TimeoutExpired:
            rmc_parse = None, None, None

        filename = os.path.basename(filename)
        print_output(filename, rmc_parse)
        tex = tex + "\\emph{{{0}}} & {1} & {2} \\\\\n\\midrule\n".format(filename, \
            format_output(rmc_parse[0]), format_output(rmc_parse[1]))

    tex += "\\end{tabular}\n\\end{table}"
    if texout:
        print(tex)


def parse_output(output):
    lines = output.split('\n')
    lines = list(filter(None, lines)) #Remove empty lines
    sat = lines[SATLINE]
    model_check = str()
    if sat == "Sat":
        match = re.search("Model check: ([a-zA-Z]+)", lines[MODEL_CHECK])
        model_check = match.group(1)
    match = re.search("Time: ([0-9]+.[0-9]+)", lines[TIMELINE])
    time = round(float(match.group(1)), 2)
    return sat, time, model_check


def print_config(formulas):
    print("Timeout: {0}".format(TIMEOUT))
    print("Number of formulas: {0}".format(formulas))


def format_output(parse):
    return "{0}".format("TO" if parse is None else parse)


def print_output(filename, rmc_parse):
    print("{0}: {1}\t {2}\t {3}".format(filename, format_output(rmc_parse[0]), \
        format_output(rmc_parse[1]), format_output(rmc_parse[2])))


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./experimental [bin]"\
        "[formula folder] [--tex] [--formulas=X]\n")


if __name__ == "__main__":
    main()
