#!/usr/local/bin/python3
#This script runs HiFrog twice (first bootstraping phase, and second upgrade cheking) and then
# checks the expected results. It also dumps the verification results into a collected*.txt file 
#Note that we define config files for only original files and we specify what is their next revisions.

#usage: python3 run_tests.py <hifrog-executable-path>

import subprocess
import os
import sys
import argparse
from datetime import datetime

RED   = "\033[1;31m"
BLUE  = "\033[0;34m"
BLUE_bold  = "\033[1;34m"
BLACK  = "\033[1;30m"
RESET = "\033[0;0m"
GREEN = "\033[1;32m"
WARNING = '\033[33m'

def filtercomments(input_text):
    comment_start = ';'
    filtered = [ line for line in input_text.splitlines() if not line.startswith(comment_start) ]
    return '\n'.join(filtered)

def cleaning():
    summaries_name = '__summaries'
    omega_name = '__omega'
    summaries_path = os.path.join(scriptpath, summaries_name)
    omega_path = os.path.join(scriptpath, omega_name)
    if os.path.exists(summaries_path):
        os.remove(summaries_path)
        print("removed old summary! ")
    if os.path.exists(omega_path):
        os.remove(omega_path)
        print("removed old omega! ")    
    if os.path.exists(scriptpath+"/__summaries"):
        os.remove(scriptpath+"/__summaries")
        print("removed old summary in scriptpath! ")
    if os.path.exists(scriptpath+"/__omega"):
        os.remove(scriptpath+"/__omega")
        print("removed old omega in scriptpath! ") 

# 4 -------------------------------------------------------
def run_upgrade_check(newargs, shouldSuccess, scriptpath, testname):
    #rerun with the computed summaries
    command = ' '.join(newargs)
    title('Upgrade Checking Phase:'),
    note(command)
    out = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    stdoutput = out.stdout.decode('utf-8')  #Second output with reusing summary
    stderror = out.stderr.decode('utf-8')
    filteredOutput = filtercomments(stdoutput)
    print(filteredOutput)
    print(stderror)
    collect_data(stdoutput, stderror, testname, command)  # collect rerun time and results;
    
    # get the line containing the verification result
    resultLines = [line for line in filteredOutput.splitlines() if "VERIFICATION" in line]
    if not resultLines:
        resultLines = [line for line in filteredOutput.splitlines() if "VERIFICATION SUCCESSFUL" in line]
        error('The upgrade checking did not return verification result!')
        warning(resultLines)
        return False
    if len(resultLines) > 1:
        warning('The upgrade checking did not finish in one iteretion!')
        warning(resultLines)
        #return False
    #get the last element of list
    resultLine = resultLines[-1]
    expectedResult = "VERIFICATION SUCCESSFUL" if shouldSuccess else "VERIFICATION FAILED"
    testPassed = (resultLine == expectedResult)
    if not testPassed:
        error('Test result is different than the expected one!')
        return False
    else:
        success('As expected upgrade checking!')

    cleaning()
    '''
    if resultLine != expectedResult:
        error('The upgrade checking verification was not successful')
        return False
    
    #get the line containing the number of iteration
    iterationlines = [line for line in filteredOutput.splitlines() if 'Total number of steps' in line]
    if len(iterationlines) != 1:
        error("The output of upgrade checking does not contain information about the number of iteration")
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
    success('successful upgrade checking with reusing summaries !')
    '''
# 3 -------------------------------------------------------
def run_bootstrapping(args, shouldSuccess, scriptpath, testname):
    computes_summaries = (('--no-itp' not in args) and ('--theoref' not in args))  
    cleaning()
    newargs = args
    command = ' '.join(newargs)
    title('Bootstraping phase:'),
    note(command)
    out = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    stdoutput = out.stdout.decode('utf-8')   #First output
    stderror = out.stderr.decode('utf-8')
    filteredOutput = filtercomments(stdoutput)
    print(filteredOutput) #log
    print(stderror) #time appears here
    # collect verification time and results; dump the results in collected*.txt
    collect_data(stdoutput, stderror, testname , command)
    # get the line containing the verification result
    resultLines = [line for line in filteredOutput.splitlines() if "VERIFICATION" in line]
    if not resultLines:
        error("No verification result! --> " + testname)
        warning(resultLines)
        return False
    if len(resultLines) > 1:
        warning("Got multiple lines with verification result when only one was expected!")
        warning(resultLines)
        return False
    resultLine = resultLines[0]
    expectedResult = "VERIFICATION SUCCESSFUL" if shouldSuccess else "VERIFICATION FAILED"
    testPassed = (resultLine == expectedResult)
    if not testPassed:
        error('Bootstraping  result does not match the expected one! --> '+ testname)
        return False
    success('As expected bootstrapping phase!')
    if (not shouldSuccess) or (not computes_summaries):
        return True
    return True
# 2 -------------------------------------------------------
# for a given configuration file, we look for the source file and 
#run hifrog on that source file for each configuratiom found in config file
def run_test_case(options, testdir, configfile):
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
    args_general= ''
    path_to_exec = options.executable
#    z3_allowed = options.z3
    flag = True
    for configuration in configurations:
        # ignore empty lines or lines starting wiht '#' -> comments
        if not configuration or configuration.startswith('#'):
            continue
        # ignore lines or lines containing logic prop
        if "logic prop" in configuration:
            continue    
        fields = configuration.split(separator)
        if len(fields) < 2:
            error('Configuration not in correct format: ' + configuration)
            error('bad config file is: '+ configpath +' for -->  '+ testname)  
            continue    
        if configuration.startswith("--init-upgrade-check"):
            # global arguments for both bootstraping and upgrade_checking; the first starts with --init-upgrade-check
            args_general = fields[0].strip().split()
             # expected result
            exp_res = fields[1].strip()
            res = run_bootstrapping([path_to_exec] + args_general + [sourcepath], should_success(exp_res), scriptpath, testname)
            flag = True
        elif configuration.startswith("--do-upgrade-check"):
            if(flag == True):
                args_general = args_general[1:]
                args_upgrade = args_general + fields[0].strip().split()
                # expected result
                exp_res = fields[1].strip()
                res = run_upgrade_check([path_to_exec] + args_upgrade + [sourcepath], should_success(exp_res), scriptpath, testname)
                flag = False
 #      if 'z3' in args and not z3_allowed:
 #          continue
        
        if not res:
            fail_count = fail_count + 1
        print('')
    return fail_count == 0

# 1-------------------------------------------------------
def run(options):
    # where the testcases are located
    testdir = './testcases'
    fails_in_tests = 0
    # process each configuration file you find there
    for subdirs, dirs, files in os.walk(testdir):
        for file in files:
            if file.endswith('.conf'):
                title_black('--- Checking ' + file + ' --- ')
                res = run_test_case(options, testdir, file)
                if not res:
                    fails_in_tests = fails_in_tests + 1
    print('')
    note('Result of this test suite:\n')
    if fails_in_tests > 0:
        error('There were some failed tests!')
 #       error('Number of failed tests: ' + str(fails_in_tests))
    else:
        success('All tests ran successfully!')
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
def collect_data(fullLog, timeLog, testname, strarg):  #fullLog is string!
    fout = open(scriptpath+"/collected_" + datestring + ".txt", 'a')
    fout.write( testname)
    time=''
    res=''
    errormsg=''

    for line in timeLog.split('\n'):
        if line.find("user ")!=-1:
            time=line[5:]
            fout.write(time)

    for line in fullLog.split('\n'):
        if line.find("VERIFICATION SUCCESSFUL")!=-1:
            res=' UNSAT '
            fout.write(res)
        if line.find("VERIFICATION FAILED")!=-1:
            res=' SAT ' 
            fout.write(res)

    for line in timeLog.split('\n'):
        if line.find("CPU time limit exceeded")!=-1:
            errormsg=' Timeout!'
        if line.find("OutOfMemoryException")!=-1 or line.find( "MEMORY LIMIT EXCEEDED")!=-1 or line.find("Out of memory")!=-1:
            errormsg=' Memory-out!'
        if line.find("Command terminated by signal 6")!=-1:
            errormsg=' terminated_by_signal_6!'

        elif line.find("Command terminated by signal 24")!=-1:
            errormsg=' terminated_by_signal_24!'

        elif line.find("terminated by signal 2")!=-1:
            errormsg=' terminated by signal 2!'

        elif line.find( "Command terminated")!=-1:
            errormsg=' terminated_abnormally!'

        elif line.find("Assertion(s) hold trivially.")!=-1:
            errormsg=' trivially_Holds '

        elif line.find("Assertion is not reachable")!=-1:
            errormsg=' not_reachable_Assertion '
        elif line.find("Failed to deserialize previous verification efforts")!=-1:
            errormsg= ' no __omega! '
        if errormsg !='':
            fout.write(errormsg)
            res=''
            errormsg=''   
        #if line.find("Done")!=-1:   
        #    res=''
        #    errormsg='' 
        #    time=''
    fout.write('\n')
    fout.close()
    return True 
#-------------------------------------------------------
def note(text):
    sys.stdout.write(BLUE)
    print(text)
    sys.stdout.write(RESET)

def title(text):
    sys.stdout.write(BLUE_bold)
    print(text)
    sys.stdout.write(RESET)

def title_black(text):
    sys.stdout.write(BLACK)
    print(text)
    sys.stdout.write(RESET)

def success(text):
    sys.stdout.write(GREEN)
    print(text)
    sys.stdout.write(RESET)


def error(text):
    sys.stdout.write(RED)
    print(text)
    sys.stdout.write(RESET)
    error.counter += 1
    print("ERROR! Total number of errors so far: ", error.counter-1)
error.counter = 0
    

def warning(text):
    sys.stdout.write(WARNING)
    print(text)
    sys.stdout.write(RESET)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--executable", help="path to HiFrog executable", default="./hifrog")
    parser.add_argument("--timeout", help="Set the timeout for each run (in seconds)", type=int, default=120)
#    parser.add_argument("--z3", help="Enables testing also with z3 solver", action="store_true")
    args = parser.parse_args()
    #print(args.executable)
    #print(args.z3)

    pathname = os.path.dirname(sys.argv[0])
    scriptpath= os.path.abspath(pathname)

    datestring = datetime.strftime(datetime.now(), '%Y.%m.%d_%H:%M')
    args.executable = ' ulimit -Sv 12000000; ulimit -St ' + str(args.timeout) + '; /usr/bin/time -p ' + args.executable    #print(args.executable)
    run(args)

