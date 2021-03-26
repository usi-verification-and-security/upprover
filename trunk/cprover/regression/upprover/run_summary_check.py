#!/usr/local/bin/python3
'''
dumps summary of bootstrapping phase in a 'summary_folder' and you can later watch it
usage: python3 run_summary_check.py --executable <path_to_UPPROVER_exe>'
'''

import subprocess
import os
import sys
import argparse  #Parser for command-line options
from datetime import datetime
from pathlib import Path
import time

RED   = "\033[1;31m"
BLUE  = "\033[0;34m"
BLUE_bold  = "\033[1;34m"
BLACK  = "\033[1;30m"
RESET = "\033[0;0m"
GREEN = "\033[1;32m"
WARNING = '\033[33m'

def makeDirectory(path_to_directory):
    p = Path(path_to_directory)
    if not os.path.exists(path_to_directory):
        p.mkdir()
        print("created path: ", path_to_directory)
    else:
        print("path already exists: ", path_to_directory)
        sys.exit(1)

def filtercomments(input_text):
	comment_start = ';'
	filtered = [ line for line in input_text.splitlines() if not line.startswith(comment_start) ]
	return '\n'.join(filtered)

#move to a directory called summary
def moving(testname):
	summaries_name = '__summaries'
	omega_name = '__omega'
	summaries_path = os.path.join(scriptpath, summaries_name)
	omega_path = os.path.join(scriptpath, omega_name)
	if os.path.exists(summaries_path):
		# os.remove(summaries_path)
		os.replace(scriptpath+"/__summaries", summary_folder+ "/__summaries_" + testname)
		print("moved old summary! ")

	if os.path.exists(omega_path):
		os.remove(omega_path)
		print("removed old omega! ")

	if os.path.exists(scriptpath+"/__summaries"):
		# os.remove(scriptpath+"/__summaries")
		os.replace(scriptpath+"/__summaries", summary_folder + "/__summaries_" + testname)
		print("moved old summary! ")
	
	if os.path.exists(scriptpath+"/__omega"):
		os.remove(scriptpath+"/__omega")
		print("removed old omega in scriptpath! ") 

def cleaning():
	summaries_name = '__summaries'
	omega_name = '__omega'
	summaries_path = os.path.join(scriptpath, summaries_name)
	omega_path = os.path.join(scriptpath, omega_name)
	if os.path.exists(summaries_path):
		os.remove(summaries_path)
		print("moved old summary! ")

	if os.path.exists(omega_path):
		os.remove(omega_path)
		print("removed old omega! ")

	if os.path.exists(scriptpath+"/__summaries"):
		os.remove(scriptpath+"/__summaries")
		print("moved old summary! ")
	
	if os.path.exists(scriptpath+"/__omega"):
		os.remove(scriptpath+"/__omega")
		print("removed old omega in scriptpath! ") 
# -------------------------------------------------------
def run_bootstrapping(args, shouldSuccess, scriptpath, testname):
	computes_summaries = (('--no-itp' not in args) and ('--theoref' not in args))  
	cleaning()
	time.sleep(3) #sometime rm command takes a while to delete summaries 
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

	moving(testname)
	return True
# -------------------------------------------------------
# for a given configuration, run upprover on the corresponding source file
def run_test_case(options, testdir, configfile):
	# name of the test from config file without the .conf extension
	testname = configfile[:-5]
	# name of the source file
	sourcefile = testname + '.c'
	# prepare source file to be in the given directory
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
		try:
			# ignore empty lines or lines starting wiht '#' -> comments
			if not configuration or configuration.startswith('#'):
				continue
			# ignore lines or lines containing logic prop
			if "logic prop" in configuration:
				continue
			if "logic qfuf" in configuration:
				continue
			fields = configuration.split(separator)
			if len(fields) < 2:
				error('Configuration not in correct format: ' + configuration)
				error('bad config file is: '+ configpath +' for -->  '+ testname)  
				continue    
			if configuration.startswith("--bootstrapping"):
				# global arguments for both bootstraping and summary validation phase; the first starts with --bootstrapping
				args_general = fields[0].strip().split()
				 # expected result
				exp_res = fields[1].strip()
				res = run_bootstrapping([path_to_exec] + args_general + [sourcepath], should_success(exp_res), scriptpath, testname)
				flag = True
			elif configuration.startswith("--summary-validation"):
				continue
				#if 'z3' in args and not z3_allowed:
				#	continue
			if not res:
				fail_count = fail_count + 1
			print('')
		except Exception as e:
			print("Unexpected Error is catched for this file: ", configuration)
			print(e)

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
		error('The number of failed tests are: ')
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

	if (len(sys.argv) < 2):
		print("Usage: %s --executable <path-to-executable>" % sys.argv[0])
		sys.exit(1)
	parser = argparse.ArgumentParser()
	parser.add_argument("--executable", help="path to UpProver executable", default="./upprover")
	parser.add_argument("--timeout", help="Set the timeout for each run (in seconds)", type=int, default=120)
#   parser.add_argument("--z3", help="Enables testing also with z3 solver", action="store_true")
	args = parser.parse_args()

	pathname = os.path.dirname(sys.argv[0])
	scriptpath= os.path.abspath(pathname)

	#store where-single-shell-go
	summary_folder = scriptpath + "/" + "summary_folder"
	makeDirectory(summary_folder)

	args.executable = ' ulimit -Sv 12000000; ulimit -St ' + str(args.timeout) + '; /usr/bin/time -p ' + args.executable
	run(args)
	print("Done! Check summaries stored in ",  summary_folder)
