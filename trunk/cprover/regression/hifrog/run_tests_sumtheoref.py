#!/usr/bin/env python3

#usage: python3 run_tests.py <hifrog-executable-path>

import subprocess
import os
import sys
import re
from datetime import datetime

RED   = "\033[1;31m"
BLUE  = "\033[0;34m"
RESET = "\033[0;0m"
GREEN = "\033[1;32m"

def filtercomments(input_text):
    comment_start = ';'
    filtered = [ line for line in input_text.splitlines() if not line.startswith(comment_start) ]
    return '\n'.join(filtered)

def purge(dir, pattern):
    for f in os.listdir(dir):
        if re.search(pattern, f):
            os.remove(os.path.join(dir, f))
            
#-------------------------------------------------------
def run_single(path_to_bin, configs_str, path_to_test):
    #note("Running test: " + path_to_test)
    command = path_to_bin + ' --sum-theoref ' + path_to_test
    note("Running test: " + command)
    out = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    stdoutput = out.stdout.decode('utf-8')
    filteredOutput = filtercomments(stdoutput)
    resultLines = [line for line in filteredOutput.splitlines() if "VERIFICATION" in line]
    refinementLines = [line for line in filteredOutput.splitlines() if 'verified by ' in line]
    configs = configs_str.split('\n')
    claim = 0
    incorrect = 0
    wrong_level = 0
    refinementLine = 0
    for config_line in configs:
        config_line.strip()
        if not config_line:
            continue
        fields = config_line.split(';')
        fields = list(map(str.strip, fields))
        assert(fields[0] == 'sum-theoref')
        claim_field = fields[1]
        expected_str = fields[2]
        logic_field = fields[3]
        expected = should_succeed(expected_str)
        res = resultLines[claim]
        failed =  (res != "VERIFICATION SUCCESSFUL") if expected else (res != "VERIFICATION FAILED")
        if failed:
            incorrect = incorrect + 1
        if expected :
            levelLine = refinementLines[refinementLine]
            refinementLine = refinementLine + 1
            if not logic_field in levelLine.lower():
                wrong_level = wrong_level + 1
        claim = claim + 1
    if incorrect > 0:
        error("Some claims returned different results then they should!")
        return False
    if wrong_level > 0:
        error("Some claims were verified on a different level than expected!")
        return False
    assert(incorrect == 0 and wrong_level == 0)
    success("Test successful!")
    return True
        

#-------------------------------------------------------
def run(path_to_exec):
    # where the testcases are located
    testdir = './testcases-sumtheoref'
    fails_in_tests = 0
    purge('./', '^__summaries.*')
    # process each configuration file you find there
    for subdirs, dirs, files in os.walk(testdir):
        for file in files:
            if file.endswith('.conf'):
                res = run_test_case(path_to_exec, testdir, file)
                purge('./', '^__summaries.*')
                if not res:
                    fails_in_tests = fails_in_tests + 1
    print('')
    note('Result of this test suite:\n')
    if fails_in_tests > 0:
        error('There were some failed tests!')
        error('Number of failed tests: ' + str(fails_in_tests))
    else:
        success('All tests ran successfully!')

#-------------------------------------------------------
# for a given configuration file, we look for the source file and 
#run hifrog on that source file for each configuratiom found in config file
def run_test_case(path_to_exec, testdir, configfile):
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
        configurations = cfg.read()
        return run_single(path_to_exec, configurations, sourcepath)
    

#-------------------------------------------------------
# maps string representation of expected result to boolean
def should_succeed(expected):
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
    exec_path = './hifrog'
    if len(sys.argv) > 1:
        exec_path = sys.argv[1]
    pathname = os.path.dirname(sys.argv[0])
    mypath= os.path.abspath(pathname)
    datestring = datetime.strftime(datetime.now(), '%Y.%m.%d_%H:%M')
    exec_path=' ulimit -Sv 12000000; ulimit -St 300; /usr/bin/time -p ' + exec_path 
    run(exec_path)

