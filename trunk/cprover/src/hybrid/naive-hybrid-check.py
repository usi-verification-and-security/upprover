#!/usr/bin/python
# -*- coding: utf8 -*-

import operator
import os
import sys
import subprocess

class AssertionTypes:
    Trusted, Untrusted = range(2)

class AssertionStates:
    Unknown, Valid, Invalid = range(3)


# Inputs the assertions in the file
def process_file (filename, input_path, output_path, assertions):
    # Sort the assertions first
    assertions.sort(key=operator.itemgetter(0))

    # Copy the files while inserting the assertions
    f1 = open(input_path + filename, 'r');
    f2 = open(output_path + filename, 'w');
    line = f1.readline()
    srcline = 1
    assertion_idx = 0
    assertion_line, assertion_expr, assertion_type, assertion_state = assertions[assertion_idx]

    # Copy files line by line and insert the assertions at the appropriate locations
    while line:
        # Output the assertions first
        while assertion_line == srcline:
            if assertion_state != AssertionStates.Invalid:
                f2.write(assertion_expr)
                f2.write("\n")

            assertion_idx += 1

            if assertion_idx >= len(assertions):
                assertion_idx = -1 # No more assertions
                assertion_expr = None
            assertion_line, assertion_expr, assertion_type, assertion_state = assertions[assertion_idx]

        # Output the original line
        f2.write(line)
        srcline += 1
        line = f1.readline()
    f2.close()
    f1.close()

# Injects assertions into the given file
def inject_assertions (filename, input_path, output_path, assertions):
    print (" * Unimplemented")

# Runs goto-cc to create a goto-binary models for the input files
def create_models (files, output_path):
    # Choose the correct executable for each platform
    if sys.platform == 'win32':
        cmd_str = ["goto-cl.exe", "/Fo" + output_path + "a.out"]
    elif sys.platform == 'cygwin':
        cmd_str = ["goto-cc.exe", "-o", output_path + "a.out"]
    else:
        cmd_str = ["goto-cc", "-o", output_path + "a.out"]

    cmd_str.extend(map(lambda x: (output_path + x), files))

    print (" * Running:")
    print (cmd_str);

    proc = subprocess.Popen(cmd_str, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ)

    std_out, std_err = proc.communicate()

    # Finished correctly?
    if proc.returncode > 0:
        print (" * Error during running goto-cc")
        sys.stderr.write(std_err.decode("ascii"))
        sys.stdout.write(std_out.decode("ascii"))
        return False

    # no problem during the execution
    return True


# Performs a single evolcheck run on a given set of assertions
# using a given set of summaries
def run_evolcheck (filename, input_path, output_path, assertions):
    result_str = os.popen('evolcheck ...').read()

# Performs a repeated check
def check_all_assertions (filename, input_path, output_path, assertions):
    print (" * Unimplemented")

# Parses an assertion file
def parse_assertions (assertion_file, assertion_map, assertion_type):
    f1 = open(assertion_file, 'r');
    line = f1.readline()

    while line:
        arr = line.split('\t',3)
        if len(arr) == 3:
            filename = arr[0]
            line_number = int(arr[1])
            expr = arr[2].strip()
            # print ('Assertion: file=%s, line=%s, expression="%s"' % (filename, line_number, expr))
            if not assertion_map.__contains__(filename):
                assertion_map[filename] = []
            assertion_map[filename].append( (line_number, expr, assertion_type, AssertionStates.Unknown) )
        else:
            print ('ERROR: unexpected line in the assertions file "%s"' % line)
        line = f1.readline()
    f1.close()

    
# Check parameters
if len(sys.argv) < 6:
    print ("Expected at least 5 arguments")
    print ("")
    print ("Usage")
    print ("naive-hybrid-check.py [trusted_assertion_file] [untrusted_assertion_file] [input_path] [tmp_path] [file1] [file2] ...")
    sys.exit(1)


# Maps file names to the oredered lists of assertions (line,expression,type,state)
assertion_map = {}

# Input files with assertions and the paths
trusted_assertions_file = sys.argv[1]
untrusted_assertions_file = sys.argv[2]
input_path = sys.argv[3] + os.sep
output_path = sys.argv[4] + os.sep
files = sys.argv[5:]

# Parse the file with untrusted assertions
parse_assertions(untrusted_assertions_file, assertion_map, AssertionTypes.Untrusted)

# Parse the file with trusted assertions
parse_assertions(trusted_assertions_file, assertion_map, AssertionTypes.Trusted)


# Process the files
for filename in files:
    print (' * Processing file: %s' % filename)
    process_file(filename, input_path, output_path, assertion_map[filename])

create_models(files, output_path)

print (' * Done.')


