import os
import sys

if __name__ == '__main__':
	build_output_results = sys.argv[1]   #path for facts written in .smt2 files 
	pathname = os.path.dirname(build_output_results)
	mypath= os.path.abspath(pathname)+"/"+build_output_results
      
	from os import listdir
	from os.path import isfile, join
	onlyfiles = [f for f in listdir(mypath) if isfile(join(mypath, f))]
	fi=open(mypath+"/result.txt", 'w')
	for f in onlyfiles:
		if f.split('.')[-1]=='txt':
			flog=open(mypath+"/"+f, 'r')
			res=''
			flogLines=flog.readlines()
			for line in flogLines:
				if line.find("sat")!=-1:
					res='SAT'
				if line.find("unsat")!=-1:
		                	res='UNSAT' 
				
			print "\n" + "checking", f 
 			if res!='':
                              	fi.write(res.strip("/n"))
                               	fi.write("  ")
				fi.write(f.strip("/n"))
                       		fi.write("  ")
				fi.write("\n")
				print res.strip("/n")
                       	else:
                               	fi.write(" NoResult")
                               	fi.write("  ")
				print "NoResult",
				fi.write(f.strip("/n"))
                                fi.write("  ") 
				fi.write("\n")
			flog.close()
	fi.close()
