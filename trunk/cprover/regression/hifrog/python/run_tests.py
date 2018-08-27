#!/usr/local/bin/python3
#This script runs HiFrog twice(first without summary and second with reusing the summary) and then
# checks with the expected results. It also dumps the verification results into a collected*.txt file 

#usage: python3 run_tests.py <hifrog-executable-path>

import subprocess
import os
import sys
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
def run_single(args, shouldSuccess, folderpath, testname):
    computes_summaries = (('--no-itp' not in args) and ('--theoref' not in args))
    summaries_name = '__summaries'
    summaries_path = os.path.join(folderpath, summaries_name)
    if os.path.exists(summaries_path):
        os.remove(summaries_path)
    newargs = args + ['--save-summaries', summaries_path]
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
    if not resultLines:
        error("No verification result! --> " + testname)
        return False
    if len(resultLines) > 1:
        error("Got multiple lines with verification result when only one was expected!")
        return False
    resultLine = resultLines[0]
    expectedResult = "VERIFICATION SUCCESSFUL" if shouldSuccess else "VERIFICATION FAILED"
    testPassed = (resultLine == expectedResult)
    if not testPassed:
        error('Test result is different than the expected one! --> '+ testname)
        return False
    success('Test result as expected!')
    if (not shouldSuccess) or (not computes_summaries):
        return True

    #rerun with the computed summaries
    assert os.path.exists(summaries_path), 'Summaries for rerun not found!'
    newargs = newargs + ['--load-summaries', summaries_path]
    command = ' '.join(newargs)
    note('Reruning the command to check the summaries:' + command)
    out = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    stdoutput = out.stdout.decode('utf-8')  #Second output with reusing summary
    stderror = out.stderr.decode('utf-8')
    filteredOutput = filtercomments(stdoutput)
    collect_data(stdoutput, testname, command)  # collect rerun time and results;
    
    # get the line containing the verification result
    resultLines = [line for line in filteredOutput.splitlines() if "VERIFICATION" in line]
    if not resultLines:
        error('The rerun did not return verification result!'+ testname)
        return False
    if len(resultLines) > 1:
        error('The rerun did not finish in one iteretion!')
        return False
    resultLine = resultLines[0]
    if resultLine != expectedResult:
        error('The rerun verification was not successful')
        return False
    #get the line containing the number of iteration
    iterationlines = [line for line in filteredOutput.splitlines() if 'Total number of steps' in line]
    if len(iterationlines) != 1:
        error("The output of rerun does not contain information about the number of iteration")
        return False
    iter_split = iterationlines[0].split(":")
    if len(iter_split) < 2:
        error("Cannot get the number of iterations!")
        return False
    iteration_count = int(iter_split[1])
    if iteration_count > 1:
        error("Summaries were not re-used successfully and refinement occured!")
        return False
    if iteration_count != 1:
        error("Weird situation with number of iterations!")
        return False
    success('Re-verification with summaries successful!')
    os.remove(summaries_path)
    return True
#-------------------------------------------------------
def run(path_to_exec):
    # where the testcases are located
    testdir = './testcases'
    fails_in_tests = 0
    # process each configuration file you find there
    for subdirs, dirs, files in os.walk(testdir):
        for file in files:
            if file.endswith('.conf'):
                res = run_test_case(path_to_exec, testdir, file)
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
        configurations = cfg.read().splitlines()
    # each configuration on one line, arguments separated from expected result by ';'
    separator = ';'
    fail_count = 0
    for configuration in configurations:
        # ignore empty lines or lines starting wiht '#' -> comments
        if not configuration or configuration.startswith('#'):
            continue
        fields = configuration.split(separator)
        if len(fields) < 2:
            error('Configuration not in correct format: ' + configuration)
            error('bad config file is: '+ configpath +' for -->  '+ testname)  
            continue
        # arguments with which to run hifrog
        args = fields[0].strip().split()
        # expected result
        exp_res = fields[1].strip()
        res = run_single([path_to_exec] + args + [sourcepath], should_success(exp_res), testdir, testname)
        if not res:
            fail_count = fail_count + 1
        print('')
    return fail_count == 0
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
    exec_path = './hifrog'
    if len(sys.argv) > 1:
        exec_path = sys.argv[1]
    pathname = os.path.dirname(sys.argv[0])
    mypath= os.path.abspath(pathname)
    datestring = datetime.strftime(datetime.now(), '%Y.%m.%d_%H:%M')
    exec_path=' ulimit -Sv 12000000; ulimit -St 120; /usr/bin/time -p ' + exec_path 
    run(exec_path)

