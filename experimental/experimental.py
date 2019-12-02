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
from enum import Enum

SATLINE = -2
TIMELINE = -1
MODEL_CHECK = -3
TIMEOUT = 10 #in seconds
FORMULAS = 1000

class ToolType(Enum):
    RMC = 1
    Z3 = 2
    CVC4 = 3



def main():
    #Input parsing
    if len(sys.argv) < 4:
        help_err()
        sys.exit()
    try:
        opts, args = getopt.getopt(sys.argv[3:], "tf:", ["tex", "formulas=", "rmc", "z3", "cvc4"])
    except getopt.GetoptError as err:
        help_err()
        sys.exit()

    bin = sys.argv[1]
    formulafolder = sys.argv[2]
    texout = False
    tool = None
    FORMULAS = 1000

    for o, a in opts:
        if o in ("-t", "--tex"):
            texout = True
        if o in ("-f", "--formulas"):
            FORMULAS = int(a)
        if o in ("--rmc"):
            tool = ToolType.RMC
        if o in ("--z3"):
            tool = ToolType.Z3
        if o in ("--cvc4"):
            tool = ToolType.CVC4

    if tool is None:
        print("Tool must be specified")
        sys.exit()


    print_fnc = None
    parse_fnc = None
    args = []
    if tool == ToolType.RMC:
        print_fnc = print_output_rmc
        parse_fnc = parse_output_rmc
        args = ["../automata/rrt-x-yx-len.vtf", "../automata/rrt-x-eps-len.vtf", "../automata/rrt-x-yx.vtf", "../automata/rrt-x-eps.vtf"]
    elif tool == ToolType.Z3:
        print_fnc = print_output
        parse_fnc = parse_output_z3
        args = ["-st"]
    elif tool == ToolType.CVC4:
        print_fnc = print_output
        parse_fnc = parse_output_cvc4
        args = ["--stats"]


    #Experiments

    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".smt2")]
    files.sort()
    files = files[:FORMULAS]

    print_config(FORMULAS)
    print("Formula: time, sat")

    for eq_file in files:
        filename = os.path.join(formulafolder, eq_file)

        try:
            output = subprocess.check_output([bin, filename]+args, \
                timeout=TIMEOUT, stderr=subprocess.STDOUT).decode("utf-8")
            parse = parse_fnc(output)
        except subprocess.TimeoutExpired:
            parse = None, None, None

        filename = os.path.basename(filename)
        print_fnc(filename, parse)


def parse_output_rmc(output):
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


def print_output_rmc(filename, rmc_parse):
    print("{0}: {1}\t {2}\t {3}".format(filename, format_output(rmc_parse[0]), \
        format_output(rmc_parse[1]), format_output(rmc_parse[2])))


def print_output(filename, parse):
    print("{0}: {1}\t {2}".format(filename, format_output(parse[0]), format_output(parse[1])))


def parse_output_z3(output):
    lines = output.split('\n')
    lines = list(filter(None, lines)) #Remove empty lines
    sat = False
    if lines[0] == "sat":
        sat = True
    time = None
    for line in lines:
        match = re.search(r':total-time[\s]+([0-9]+.[0-9]+)', line)
        if match is not None:
            time = round(float(match.group(1)), 2)
            break
    return sat, time


def parse_output_cvc4(output):
    lines = output.split('\n')
    lines = list(filter(None, lines)) #Remove empty lines
    sat = False
    if lines[0] == "sat":
        sat = True
    time = None
    for line in lines:
        match = re.search(r'driver::totalTime, ([0-9]+.[0-9]+)', line)
        if match is not None:
            time = round(float(match.group(1)), 2)
            break
    return sat, time


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./experimental [bin]"\
        "[formula folder] [--tex] [--formulas=X]\n")


if __name__ == "__main__":
    main()
