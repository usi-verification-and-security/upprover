#First run $ bash testcases_perf.sh > testcases_perf.txt 2>&1
# Then run this script python3 collect_data.py
# This script collects time and error message from the logfile that has been already generated in testcases_perf.txt and 
#reports the colected data in upg_time.txt

import os
import sys

if __name__ == '__main__':
		pathname = os.path.dirname(sys.argv[0])
		mypath= os.path.abspath(pathname)
		fout = open(mypath+"/upg_time.txt", 'w')
		logfile = mypath+"/testcases_perf.txt"
		flog = open(logfile, 'r')
		time=''
		res=''
		bench_sets=''
		errormsg=''
		with open(logfile) as flog:
			for line in flog:
				if line.find("CHECKING TWO VERSIONS")!=-1:
					bench_sets =line[22:]	
					fout.write(bench_sets.strip('\n'))

				if line.find("CPU time limit exceeded")!=-1 or line.find( "timeout")!=-1:
					errormsg=' Timeout!'
				if line.find("OutOfMemoryException")!=-1 or line.find( "MEMORY LIMIT EXCEEDED")!=-1 or line.find("Out of memory")!=-1:
					errormsg=' Memory-out!'
				elif line.find("Command terminated by signal 6")!=-1:
					errormsg=' terminated_by_signal_6!'

				elif line.find("Command terminated by signal 24")!=-1:
					errormsg=' terminated_by_signal_24!'

				elif line.find("terminated by signal 2")!=-1:
					errormsg=' terminated by signal 2!'

				elif line.find( "Command terminated")!=-1:
					errormsg=' terminated_abnormally!'

				elif line.find("Assertion(s) hold trivially.")!=-1:
					errormsg=' trivially_Holds'

				elif line.find("Assertion is not reachable")!=-1:
					errormsg=' not_reachable_Assertion'	
				if errormsg =='':
					if line.find("user ")!=-1:
						time=line[5:]
						fout.write(time)
				else:
					fout.write(errormsg)
					res=''
					bench_sets=''
					errormsg=''	
					time=''
				if errormsg =='':
					if line.find("VERIFICATION SUCCESSFUL")!=-1:
						res=' UNSAT'
						fout.write(res)
					if line.find("VERIFICATION FAILED")!=-1:
						res=' SAT' 
						fout.write(res)
				if line.find("Done")!=-1:	
					res=''
					bench_sets=''
					errormsg=''	
					time=''
		flog.close()
		print("Check this file to see the collected data: upg_time.txt")
		fout.close()
