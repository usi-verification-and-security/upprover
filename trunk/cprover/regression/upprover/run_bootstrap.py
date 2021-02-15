#!/usr/local/bin/python3
#runing upprover in bootstrapping mode only.

#usage: python3 run_boot.py <upprover-executable-path>
#you may either give upprover exe by specifying --executable or
# copy upprover-executable in the root

import subprocess
import os
import sys
import argparse
from datetime import datetime

RED   = "\033[1;31m"
BLUE  = "\033[0;34m"
RESET = "\033[0;0m"
GREEN = "\033[1;32m"

def filtercomments(input_text):
    comment_start = ';'
    filtered = [ line for line in input_text.splitlines() if not line.startswith(comment_start) ]
    return '\n'.join(filtered)
#-------------------------------------------------------

def run_bootstrap(args, shouldSuccess, folderpath, testname):
    isBuggy=False
    summaries_name = '__summaries'
    omega_name = '__omega'
    summaries_path = os.path.join(mypath, summaries_name)
    omega_path = os.path.join(mypath, omega_name)

    try:
        if os.path.exists(summaries_path):
            os.remove(summaries_path)
            os.remove(mypath+"/__summaries")
        if os.path.exists(omega_path):
            os.remove(omega_path)
            os.remove(mypath+"/__omega")
    except:
        print('')
    newargs = args
    command = ' '.join(newargs)
    note('Executing command:' + command)
    out = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    stdoutput = out.stdout.decode('utf-8')   #First output
    stderror = out.stderr.decode('utf-8')
    filteredOutput = filtercomments(stdoutput)
    # collect verification time and results; dump the results in collected*.txt file corresponding to each arg in tescases
    collect_data(stdoutput , testname , command)
    # get the line containing the verification result
    resultLines = [line for line in filteredOutput.splitlines() if "VERIFICATION" in line]
    if not resultLines:#if resultline is empty nothing return
        error("No verification result! --> " + testname)
        return isBuggy
    elif len(resultLines) > 1:
        error("Got multiple lines with verification result when only one was expected!")
        return isBuggy
    resultLine = resultLines[0]
    expectedResult = "VERIFICATION SUCCESSFUL" if shouldSuccess else "VERIFICATION FAILED"
    testPassed = (resultLine == expectedResult)
    if not testPassed:
        error('Test result is different than the expected one! --> '+ testname)
        return isBuggy
    success('Test result as expected!')
    return not isBuggy
#rerun no need for bootstrap
#-------------------------------------------------------
def run(options):
    # where the testcases are located
    testdir = './boot_testcases'
    fails_in_tests = 0
    allBench_counts =0
    # process each configuration file you find there
    for subdirs, dirs, files in os.walk(testdir):
        for file in files:
            if file.endswith('.conf'):
                benchcounts,res = run_test_case(options, testdir, file)
                fails_in_tests = fails_in_tests + res
                allBench_counts=allBench_counts+benchcounts
    print('')
    note('Result of this test suite:\n')
    if fails_in_tests > 0:
        error('There were some failed tests!')
        error('Number of failed tests: ' + str(fails_in_tests) +' out of '+str(allBench_counts)+' benchs.')
    else:
        success('All tests ran successfully!')

#-------------------------------------------------------
# for a given configuration file, we look for the source file and
#run upprover on that source file for each configuratiom found in config file
def run_test_case(options, testdir, configfile):
    bench_counts =0
    # name of the test from config file without the .conf extension
    testname = configfile[:-5]
    # name of the source file
    sourcefile = testname + '.c'
    # source file should be in the given directory
    sourcepath = os.path.join(testdir, sourcefile)
    if not os.path.exists(sourcepath):
        error("Missing source file for test " + testname)
        print('')
        return
    # path to configuration path, we assume it exists
    configpath = os.path.join(testdir, configfile)
    with open(configpath) as cfg:
        configurations = cfg.read().splitlines()
    # each configuration on one line, arguments separated from expected result by ';'
    separator = ';'
    fail_count = 0
    path_to_exec = options.executable
    z3_allowed = options.z3
    for configuration in configurations:
        try:
            # ignore empty lines or lines starting wiht '#' -> comments
            if not configuration or configuration.startswith('#'):
                continue
            fields = configuration.split(separator)
            if len(fields) < 2:
                error('Configuration not in correct format: ' + configuration)
                error('bad config file is: '+ configpath +' for -->  '+ testname)
                continue
            # arguments with which to run upprover
            args = fields[0].strip().split()
            if '--no-itp' in args:
                continue
            if '--theoref' in args:
                continue
            if 'z3' in args and not z3_allowed:
                continue
            if 'z3' in args:
                continue
            if 'qfcuf' in args:
                continue
            if 'partial-loop' in args:
                continue
            # expected result
            exp_res = fields[1].strip()
            res = run_bootstrap([path_to_exec] + args + [sourcepath], should_success(exp_res), testdir, testname)
            bench_counts = bench_counts +1
            if not res:
                fail_count = fail_count + 1
            print('')
        except Exception as e:
            print(e)
    return bench_counts, fail_count
#-------------------------------------------------------
# maps string representation of expected result to boolean
def should_success(expected):
    if expected in ['success','succes', 'sucess']:
        return True
    if expected in ['fail', 'failed']:
        return False
    error('Incorrect expected result in config file: ' + expected)
    assert False, 'Unknown expect status'
#-------------------------------------------------------
#collects and dumps the verification results into a collected*.txt file
def collect_data(flog , testname , strarg):  #flog is string!
    fi = open(mypath+"/collected_" +datestring + ".txt", 'a')
    fi.write( testname + '.c')
    fi.write("   |  ")
    time=''
    res=''

    for line in flog.split('\n'):
        if "TOTAL TIME FOR CHECKING THIS CLAIM" in line:
            time=line.split(":")[1:][0]
        if line.find("real")!=-1:
            time=line[5:]
        if  "VERIFICATION SUCCESSFUL" in line:
            res='UNSAT'
        if  "VERIFICATION FAILED" in line:
            res='SAT'

    if res!='':
        fi.write(res.rstrip())
        fi.write("  |  ")
    else:
        fi.write(" NoResult")
        fi.write("  |  ")

    if time!='':
        fi.write(time)
        fi.write("  |  ")
    else:
        fi.write(" NoTime")

    if strarg!='':
        tmplist=strarg.split(" ")[1:]
        strarg=' '.join(tmplist)
        fi.write(strarg)
        fi.write('\n')
    else:
        fi.write(strarg)
        fi.write("no args")
        fi.write('\n')

    fi.close()
    return True
#-------------------------------------------------------
def error(text):
    sys.stdout.write(RED)
    print(text)
    sys.stdout.write(RESET)

def note(text):
    sys.stdout.write(BLUE)
    print(text)
    sys.stdout.write(RESET)

def success(text):
    sys.stdout.write(GREEN)
    print(text)
    sys.stdout.write(RESET)

if __name__ == '__main__':

    print("usage: %s --executable <path-to-upprover>" % sys.argv[0])

    parser = argparse.ArgumentParser()
    parser.add_argument("--executable", help="path to upprover executable", default="./upprover")
    parser.add_argument("--timeout", help="Set the timeout for each run (in seconds)", type=int, default=50)
    parser.add_argument("--z3", help="Enables testing also with z3 solver", action="store_true")
    args = parser.parse_args()
    pathname = os.path.dirname(sys.argv[0])
    mypath= os.path.abspath(pathname)

    datestring = datetime.strftime(datetime.now(), '%Y.%m.%d_%H:%M')
    args.executable = ' ulimit -Sv 1200000; ulimit -St ' + str(args.timeout) + '; /usr/bin/time -p ' + args.executable + " --bootstrapping "
    run(args)

