import os
import sys
if __name__ == '__main__':
	build_output = sys.argv[1]   #path for facts written in .smt2 files 
	pathname = os.path.dirname(build_output)
	mypath= os.path.abspath(pathname)+"/"+build_output
	outmypath= os.path.abspath(pathname)+"/"+"build_output_results"
	#mypath = where build_output is	

	#extract all the file in mypath
	from os import listdir
	from os.path import isfile, join
	onlyfiles = [f for f in listdir(mypath) if isfile(join(mypath, f))]
	
        
       
	for f in onlyfiles:
		pfix=f.split('.smt2')[0]
		logfile=pfix+".txt"
		cmnd = pathname+" ulimit -Sv 12000000; ulimit -St 300; /usr/bin/time -p /home/asadis/z3-4.5.0-x64-ubuntu-14.04/bin/z3 " + build_output+"/"+f +" > " + outmypath+ "/"+ logfile +" 2>&1 "
		print(cmnd)
		os.system(cmnd)
