#!/usr/bin/env python

import re
import os
import sys
import subprocess
import time

# max memory for solver in kbytes
SLVR_MMAX=4000000
USE_CBMC = False

class CheckTypes:
    Initial, Upgrade = range(2)

class AssertionTypes:
    Trusted, Untrusted = range(2)

class AssertionStates:
    Unknown, Valid, Invalid = range(3)

################################################################################ 
# Representation of an assertion injected in the code
#
class Assertion(object):

    def __init__ (self, src_line, expression, type, state, filename):
        self.__src_line = src_line
        self.__expression = expression
        self.__type = type
        self.__state = state
        self.__filename = filename
        self.__final_src_line = -1
        self.__claim_nr = -1
        self.__summarizable = True

    @property
    def src_line (self):
        return self.__src_line

    @property
    def expression (self):
        return self.__expression

    @property
    def type (self):
        return self.__type

    @property
    def state (self):
        return self.__state
    @state.setter
    def state (self, value):
        if self.__state == AssertionStates.Invalid:
            print ("ERROR: Invalidating an invalid assertion %s" % self)
            exit(1);
        self.__state = value
        if value == AssertionStates.Invalid:
            self.__final_src_line = -1

    @property
    def filename (self):
        return self.__filename

    @property
    def final_src_line (self):
        return self.__final_src_line
    @final_src_line.setter
    def final_src_line (self, value):
        self.__final_src_line = value

    @property
    def claim_nr(self):
        return self.__claim_nr
    @claim_nr.setter
    def claim_nr(self, value):
        self.__claim_nr = value

    @property
    def summarizable(self):
        return self.__summarizable
    @summarizable.setter
    def summarizable(self, value):
        self.__summarizable = value

    def __str__(self):
        return "(sl:%d, fsl:%d, ex:'%s', cnr:%s)" % (self.src_line,
                self.final_src_line, self.expression, self.claim_nr)


################################################################################ 
# Injects the Valid and Unknown assertions in the given file
#
def process_file (filename, input_path, output_path, assertions, skip_nonsummarizables):
    # Sort the assertions first
    assertions.sort(key=lambda assertion: assertion.src_line)

    # Copy the files while inserting the assertions
    input_file = open(input_path + filename, 'r');
    output_file = open(output_path + filename, 'w');
    line = input_file.readline()
    src_line = final_line = 1
    assertion_idx = 0
    if assertion_idx >= len(assertions):
        assetion = None
    else:
        assertion = assertions[assertion_idx]

    # Copy files line by line and insert the assertions at the appropriate locations
    while line:
        # Output the assertions first
        while assertion != None and assertion.src_line == src_line:
            if assertion.state != AssertionStates.Invalid and (not skip_nonsummarizables or assertion.summarizable == True):
                output_file.write("%s\n" % assertion.expression)
                assertion.final_src_line = final_line
                final_line += 1

            assertion_idx += 1
            if assertion_idx >= len(assertions):
                assertion = None
            else:
                assertion = assertions[assertion_idx]

        # Output the original line
        output_file.write(line)
        src_line += 1
        final_line += 1
        line = input_file.readline()
    output_file.close()
    input_file.close()



################################################################################ 
# Injects the assertions and prepares the goto-binary model
#
def process_files(files, input_path, output_path, assertion_map, skip_nonsummarizables):
    # Inject the assertions
    for filename in list(set(files)):
        print (' * Processing file: %s' % filename)
        process_file(filename, input_path, output_path, assertion_map[filename], skip_nonsummarizables)

    # Create goto binary
    create_models(files, output_path, assertion_map)



################################################################################ 
# Runs goto-cc to create a goto-binary model for the input files
#
def create_models (files, output_path, assertions):
    # Choose the correct executable for each platform
    if sys.platform == 'win32':
        cmd_str = ["goto-cl.exe", "/Fo" + output_path + "a.out"]
    elif sys.platform == 'cygwin':
        cmd_str = ["goto-cc.exe", "-o", output_path + "a.out"]
    else:
        cmd_str = ["goto-cc", "-o", output_path + "a.out"]

    cmd_str.extend(map(lambda x: (output_path + x), files))

#    print (" * Running:")
#    print (cmd_str);

    proc = subprocess.Popen(cmd_str, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ)

    std_out, std_err = proc.communicate()

    # Finished correctly?
    if proc.returncode > 0:
        sys.stdout.write(std_out.decode("ascii"))
        sys.stderr.write(std_err.decode("ascii"))
        print ("ERROR: Error during running goto-cc")
        exit(1)

    # no problem during the execution
    return True


################################################################################
# Get the arguments for evolcheck call based on the input arguments.
# TODO: The use of asrts is disabled, since evolcheck does not support init
# checking for the --claim-set option
#
def get_args(check_type, orig_gb, output_path, filename, asrts):
    # Choose the correct executable for each platform
    if sys.platform == 'win32' or sys.platform == 'cygwin':
        cmd_str = ["evolcheck.exe"]
    else:
        cmd_str = ["evolcheck"]

    if asrts != None and len(asrts) == 1:
        cmd_str.append("--load-summaries")
        cmd_str.append("/nonexistent/file")
#        cmd_str.append("--no-slicing")
        cmd_str.append("--claim")
        cmd_str.append("%s" % asrts[0].claim_nr)
    elif asrts != None and len(asrts) > 1:
#        TODO this is disabled for now...
#        claims = ",".join(map(lambda x: str(x.claim_nr), asrts))
#        cmd_str.append("--claim-set %s" % claims)
        pass

    # Check type
    if check_type == CheckTypes.Initial:
        if len(asrts) > 1:
            # This is a bit of a hack now, but since the user wants to check several assertions,
            # we assume that this is the place where he knows these are valid assertions
            # and he wants to make the summaries this time.
            cmd_str.append("--init-upgrade-check")
            cmd_str.append("--load-summaries")
            cmd_str.append("/nonexistent/file")
#            cmd_str.append("--no-slicing")
        cmd_str.append("--no-summary-optimization")
        cmd_str.append(output_path + filename)
    else:
#        cmd_str.append("--no-slicing")
        cmd_str.append("--do-upgrade-check")
        cmd_str.append(output_path + filename)
        cmd_str.append(orig_gb)


    return cmd_str

def get_args_cbmc(check_type, orig_gb, output_path, filename, asrts):
    # Choose the correct executable for each platform
    if sys.platform == 'win32' or sys.platform == 'cygwin':
        cmd_str = ["cbmc.exe"]
    else:
        cmd_str = ["cbmc"]

    if asrts != None and len(asrts) == 1:
#        cmd_str.append("--no-slicing")
        cmd_str.append("--claim")
        cmd_str.append("%s" % asrts[0].claim_nr)
    elif asrts != None and len(asrts) > 1:
#        TODO this is disabled for now...
#        claims = ",".join(map(lambda x: str(x.claim_nr), asrts))
#        cmd_str.append("--claim-set %s" % claims)
        pass

    cmd_str.append("--no-unwinding-assertions")

    # Check type
    if check_type == CheckTypes.Initial:
        if len(asrts) > 1:
            # This is a bit of a hack now, but since the user wants to check several assertions,
            # we assume that this is the place where he knows these are valid assertions
            # and he wants to make the summaries this time.
#            cmd_str.append("--no-slicing")
            pass
        cmd_str.append(output_path + filename)
    else:
#        cmd_str.append("--no-slicing")
        cmd_str.append(output_path + filename)


    return cmd_str

################################################################################ 
# Performs a single cbmc run on a given set of assertions
#
def run_cbmc (check_type, orig_gb, output_path, filename, assertions, claim2asrt):
    print "Running cbmc XXX"
    time_init = time.time()
    cmd_str = get_args_cbmc(check_type, orig_gb, output_path, filename, None)
    print (" * Running:")
    print (cmd_str);

    proc = subprocess.Popen(cmd_str, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ)

    std_out, std_err = proc.communicate()
    std_out_str = std_out.decode("ascii")

    dump_output("__last_out", std_out_str)
    dump_output("__last_err", std_err.decode("ascii"))

    # Finished correctly?
    if proc.returncode > 0 and proc.returncode != 10:
        print ("ERROR: Error during running cbmc (a)", proc.returncode)
        exit(1)

    std_out = None
    std_err = None

    result = analyze_cbmc_result_multi(output_path, std_out_str, assertions, claim2asrt, False)
    if result == True:
        print("Holds")
    else:
        print("Fails to hold")
#    print("Run time for evolcheck was %f" % (time.time() - time_init))
    # no problem during the execution
    return result


################################################################################ 
# Performs a single evolcheck run on a given set of assertions
# using a given set of summaries
#
def run_evolcheck (check_type, orig_gb, output_path, filename, assertions, claim2asrt):
    print "Running evolcheck XXX"
    time_init = time.time()
    cmd_str = get_args(check_type, orig_gb, output_path, filename, None)
    print (" * Running:")
    print (cmd_str);

    proc = subprocess.Popen(cmd_str, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ)

    std_out, std_err = proc.communicate()
    std_out_str = std_out.decode("ascii")

    dump_output("__last_out", std_out_str)
    dump_output("__last_err", std_err.decode("ascii"))

    # Finished correctly?
    if proc.returncode > 0:
        print ("ERROR: Error during running evolcheck (a)")
        exit(1)

    std_out = None
    std_err = None

    result = analyze_evolcheck_result_multi(output_path, std_out_str, assertions, claim2asrt, False)
    if result == True:
        print("Holds")
    else:
        print("Fails to hold")
#    print("Run time for evolcheck was %f" % (time.time() - time_init))
    # no problem during the execution
    return result

################################################################################ 
# Performs a single evolcheck run on a given set of assertions
# using a given set of summaries
#
def run_evolcheck_asrtset (check_type, orig_gb, output_path, filename, assertions, asrtlist, claim2asrt):
    print("Running evolcheck on an assertion set of %d" % len(asrtlist))
    time_init = time.time()
    cmd_str = get_args(check_type, orig_gb, output_path, filename, asrtlist)
    print (" * Running:")
    print (cmd_str);

    proc = subprocess.Popen(cmd_str, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ)

    std_out, std_err = proc.communicate()
    std_out_str = std_out.decode("ascii")

    dump_output("__last_out", std_out_str)
    dump_output("__last_err", std_err.decode("ascii"))

    # Finished correctly?
    if proc.returncode > 0:
        print ("ERROR: Error during running evolcheck (a)")
        exit(1)

    std_out = None
    std_err = None

    result = analyze_evolcheck_result(output_path, std_out_str, assertions, claim2asrt, False)

#    print("Run time for evolcheck was %f" % (time.time() - time_init))
    # no problem during the execution
    return result



################################################################################ 
# Performs a single evolcheck run on a single assertion
#
def run_evolcheck_single (check_type, orig_gb, output_path, filename, assertion, assertions, claim2asrt):
    time_init = time.time()
    cmd_str = get_args(check_type, orig_gb, output_path, filename, [assertion])

#    print (" * Running:")
#    print (cmd_str);

    cmd_new = ["sh", "-c", "ulimit -Sv %d; %s" % (SLVR_MMAX, " ".join(cmd_str))]
    print cmd_new

    proc = subprocess.Popen(cmd_new, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ) 
    std_out, std_err = proc.communicate()
    std_out_str = std_out.decode("ascii")

    dump_output("__last_out", std_out_str)
    dump_output("__last_err", std_err.decode("ascii"))

    # Finished correctly?
    mem_out = False
#    if std_err.find("GNU MP: Cannot allocate memory") != -1:
#        mem_out = True
#    elif proc.returncode > 0:
#        print ("ERROR: Error during running evolcheck (b)")
#        print std_out
#        print std_err
#        exit(1)
    if proc.returncode > 0:
        mem_out = True

    std_out = None
    std_err = None

    result = analyze_evolcheck_result(output_path, std_out_str, assertions, claim2asrt, mem_out)

#    print("Run time for evolcheck was %f" % (time.time() - time_init))
    # no problem during the execution
    return result


################################################################################ 
# Performs a single cbmc run on a single assertion
#
def run_cbmc_single (check_type, orig_gb, output_path, filename, assertion, assertions, claim2asrt):
    time_init = time.time()
    cmd_str = get_args_cbmc(check_type, orig_gb, output_path, filename, [assertion])

#    print (" * Running:")
#    print (cmd_str);

    cmd_new = ["sh", "-c", "ulimit -Sv %d; %s" % (SLVR_MMAX, " ".join(cmd_str))]
    print cmd_new

    proc = subprocess.Popen(cmd_new, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ) 
    std_out, std_err = proc.communicate()
    std_out_str = std_out.decode("ascii")

    dump_output("__last_out", std_out_str)
    dump_output("__last_err", std_err.decode("ascii"))

    # Finished correctly?
    mem_out = False
#    if std_err.find("GNU MP: Cannot allocate memory") != -1:
#        mem_out = True
#    elif proc.returncode > 0:
#        print ("ERROR: Error during running evolcheck (b)")
#        print std_out
#        print std_err
#        exit(1)
    if proc.returncode > 0:
        mem_out = True

    std_out = None
    std_err = None

    result = analyze_cbmc_result(output_path, std_out_str, assertions, claim2asrt, mem_out, assertion)

#    print("Run time for evolcheck was %f" % (time.time() - time_init))
    # no problem during the execution
    return result


################################################################################ 
# Check cbmc output for single assertion
#
def analyze_cbmc_result (output_path, std_out, assertions, claim2asrt, mem_out, assertion):
    trivial = False

    if std_out.find('VERIFICATION SUCCESSFUL') == -1:
        mark_assertion_valid(assertion)
        return True
    elif std_out.find("VERIFICATION FAILED") == -1:
        mark_assertion_invalid(assertion.filename, assertion.final_src_line, assertions)
        return False
    else:
        print (std_out)
        print ("ERROR: Unexpected cbmc output! - no VERIFICATION.")
        exit(1)

################################################################################ 
# Check cbmc output for multiple assertions
#
def analyze_cbmc_result_multi (output_path, std_out, assertions, claim2asrt, mem_out):
    trivial = False
    if std_out.find('VERIFICATION SUCCESSFUL') != -1:
        for file in assertions:
            for a in assertions[file]:
                mark_assertion_valid(a)
        return True
    elif std_out.find("VERIFICATION FAILED") != -1:
        mo = re.search("Violated property:\n[ \t]*file (.*) line ([1-9][0-9]*)", std_out, re.M)
        if mo:
            filename = mo.group(1)
            line = int(mo.group(2))
            mark_assertion_invalid(filename.replace(output_path, ""), line, assertions)
        else:
            print("ERROR parsing cbmc output: no violated property")
            exit(1)
        return False
    else:
        print (std_out)
        print ("ERROR: Unexpected cbmc output! - no VERIFICATION.")
        exit(1)


################################################################################ 
# Analyze evolcheck result on multiple assertions
#
def analyze_evolcheck_result_multi (output_path, std_out, assertions, claim2asrt, mem_out):
    trivial = False
    if std_out.find('ASSERTION IS TRUE') != -1:
        valid_claims = []
        for f in assertions:
            for cl in assertions[f]:
                mark_assertion_valid(cl)
        return True

    # An assertion failed

    m = re.search('Violated property:\n *file ' + output_path + 
            '(.*) line (.*) function .*\n *assertion[\n]* *(.*)\n', last_call_str, re.MULTILINE)

    if m == None:
        print (std_out)
        print ("ERROR: Unexpected eVolCheck output! - no Violated property")
        raise
    else:
        file = m.group(1)
        line = int(m.group(2))

#    print("Assertion violated: file %s:%d expr: %s" % (file, line, m.group(3)))

        mark_assertion_invalid(file, line, assertions)
        return False


################################################################################ 
# Analyze evolcheck result
#
def analyze_evolcheck_result (output_path, std_out, assertions, claim2asrt, mem_out):
    trivial = False
    if std_out.find('VERIFICATION') == -1:
        if std_out.find('Assertion(s) hold trivially.') != -1:
            trivial = True
        elif std_out.find('Assertion is not reachable') != -1:
            trivial = True
        elif std_out.find('ASSERTION IS TRUE') == -1:

            print (std_out)
            print ("ERROR: Unexpected eVolCheck output! - no VERIFICATION or Assertion(s) hold trivially.")
            exit(1)

    if std_out.find('OpenSMT - CNF') == -1:
        last_call_str = std_out
    else:
        split_str = std_out.rsplit('OpenSMT - CNF', 1)
        last_call_str = split_str[1]

    if (mem_out or last_call_str.find("MEMORY LIMIT EXCEEDED") != -1) and last_call_str.find('ASSERTION IS TRUE') != -1:
        # I assume we get here if assertion holds but we run out of mem while building the summary
        lines = last_call_str.split("\n")
        valid_claims = []
        for l in lines:
            m = re.search('[ \t]*Checking Claim #([0-9][0-9]*) \([0-9][0-9]*%\) ...', l)
            if m != None:
                valid_claims.append(int(m.group(1)))
        for cl in valid_claims:
            mark_assertion_valid(claim2asrt[cl])
            mark_assertion_nonsummarizable(claim2asrt[cl])
        return True

    elif last_call_str.find("VERIFICATION SUCCESSFUL") != -1 or trivial:
        lines = last_call_str.split("\n")
        valid_claims = []
        for l in lines:
            m = re.search('[ \t]*Checking Claim #([0-9][0-9]*) \([0-9][0-9]*%\) ...', l)
            if m != None:
                valid_claims.append(int(m.group(1)))
        for cl in valid_claims:
            mark_assertion_valid(claim2asrt[cl])
        return True

    m = re.search('Violated property:\n *file ' + output_path + 
            '(.*) line (.*) function .*\n *assertion[\n]* *(.*)\n', last_call_str, re.MULTILINE)

    if m == None:
        print (std_out)
        print ("ERROR: Unexpected eVolCheck output! - no Violated property")
        exit(1)

    file = m.group(1)
    line = int(m.group(2))

#    print("Assertion violated: file %s:%d expr: %s" % (file, line, m.group(3)))

    mark_assertion_invalid(file, line, assertions)
    return False

################################################################################ 
# Assertion Invalid --> remove if untrusted, report an error if trusted
#
def mark_assertion_invalid (file, src_line, assertions):
    # Mark the assertion as invalid
    match = False
    match_assertion = None

    for assertion in assertions[file]:
        if assertion.final_src_line == src_line:
            match = True
            match_assertion = assertion
            break

    if not match:
        print ("Violated assertion was not found.")
        print (src_line, file)
        for f in assertions:
            print f
            for a in assertions[f]:
                print("Assertion: %s" % a)
        raise
        exit(1)

    if match_assertion.type == AssertionTypes.Trusted:
        print("Trusted assertion violated. The upgrade is BUGGY!")
        print(match_assertion)
        exit(1)

#    print("Untrusted assertion marked as invalid")
    match_assertion.state = AssertionStates.Invalid

################################################################################ 
# Assertion Valid --> just mark it
#
def mark_assertion_valid (asrt):
    # Mark the assertion as valid
#    if asrt.type == AssertionTypes.Trusted:
#        print("Trusted assertion is valid.")
#    else:
#        print("Untrusted assertion marked as valid")
    asrt.state = AssertionStates.Valid

################################################################################ 
# Assertion unsummarizable
#
def mark_assertion_nonsummarizable (asrt):
    print ("Marking %s not summarizable" % asrt)
    asrt.summarizable = False



################################################################################ 
# Performs a single check
#
def check_all_assertions_once (check_type, orig_gb, files, input_path, output_path, assertions, claim2asrt):
    # Check the code for the asserions in a single iteration

    # Process the files
    process_files(files, input_path, output_path, assertion_map, False)

    # Run the evolcheck, in case of an assertion violation, 
    # the corresponding assertion is marked
    if USE_CBMC:
        return run_cbmc(check_type, orig_gb, output_path, "a.out", assertions, claim2asrt)
    else:
        return run_evolcheck(check_type, orig_gb, output_path, "a.out", assertions, claim2asrt)



################################################################################ 
# Count the given type of assertions
#
def count_assertions (files, assertions, assertionState):
    sum = 0
    for file in files:
        sum += reduce((lambda x, assertion: x + (1 if assertion.state == assertionState else 0)), assertions[file], 0)

    return sum


################################################################################ 
# Performs a repeated check
#
def check_all_assertions (check_type, orig_gb, files, input_path, output_path, assertions, claim2asrt):
    # Repeatedly check the code for the asserions so far
    while True:
        valid_or_unkn = count_assertions(files, assertions, AssertionStates.Valid) + count_assertions(files, assertions, AssertionStates.Unknown)
        if valid_or_unkn == 0:
            print("All assertions are invalid.")
            return False

        result = check_all_assertions_once(check_type, orig_gb, 
                files, input_path, output_path, assertions, claim2asrt)
        print("  Unknown: %d" % count_assertions(files, assertions, AssertionStates.Unknown))
        print("  Invalid: %d" % count_assertions(files, assertions, AssertionStates.Invalid))

        if result:
            print("Check succeeded!")
            print("  Valid: %d" % count_assertions(files, assertions, AssertionStates.Unknown))
            print("  Invalid: %d" % count_assertions(files, assertions, AssertionStates.Invalid))
            return True


################################################################################ 
# Search an assertion with a given final line number from an ordered list of
# assertions
#

def search(ln, asrt_list):
    low = 0
    high = len(asrt_list)
    while True:
        c = (high-low)/2 + low
        a = asrt_list[c]
        if a.final_src_line == ln:
            return c
        elif high == low:
            return -1
        elif a.final_src_line < ln:
            low = c
        elif a.final_src_line > ln:
            high = c

################################################################################ 
# Get mapping from assertions to the claims reported by evolcheck
#
def map_assertions_to_claims(output_path, assertions, c2a):
    # Choose the correct executable for each platform
    if sys.platform == 'win32' or sys.platform == 'cygwin':
        cmd_str = ["evolcheck.exe"]
    else:
        cmd_str = ["evolcheck"]

    cmd_str.append("--show-claims")
    cmd_str.append(os.path.join(output_path, "a.out"))

#    print(" * Running: %s" % cmd_str)

    proc = subprocess.Popen(cmd_str, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ)

    std_out, std_err = proc.communicate()
    std_out_str = std_out.decode("ascii")

    dump_output("__last_out", std_out_str)
    dump_output("__last_err", std_err.decode("ascii"))

    # Finished correctly?
#    if proc.returncode > 0:
#        print ("ERROR: Error during running evolcheck")
#        exit(1)

    lines = std_out.split("\n")
    while len(lines) != 0:
        line = lines[0]
        lines = lines[1:]
        mo = re.search("Claim ([1-9][0-9]*): user supplied assertion", line)
        if mo:
            cln = int(mo.group(1))
            at_str = lines[0]
            lines = lines[1:]
            guard_str = lines[0]
            lines = lines[1:]

            # The at line
            mo = re.search("At: file ([^ ]*) line ([1-9][0-9]*) function ([^ ]*)", at_str)
            if mo == None:
                print("Error finding at string: %s" % at_str)
                exit(1)
            f = mo.group(1)
            lnr = int(mo.group(2))
            fun = mo.group(3)

            # The guard line
            # 
            mo = re.search("Guard: (.*)", guard_str)
            if mo == None:
                print("Error finding guard string: %s" % asrt_str)
                exit(1)
            asrt = mo.group(1).strip()

            idx = search(lnr, assertions[os.path.basename(f)])
            if idx == -1:
                assert(False)
            else:
                assertions[os.path.basename(f)][idx].claim_nr = cln
                c2a[cln] = assertions[os.path.basename(f)][idx]


def parse_cbmc_claim(claim):
    p_claim = {'name': None, 'num': None, 'line': None}
    while (claim != ""):
#        print claim
#        print "------------"
        mo = re.search("Reading GOTO program from file", claim, re.M)
        if mo:
            claim = claim[mo.end(0):]
            continue
        mo = re.search("Function Pointer Removal", claim)
        if mo:
            claim = claim[mo.end(0):]
            continue
        mo = re.search("Generic Property Instrumentation", claim)
        if mo:
            claim = claim[mo.end(0):]
            continue

        mo = re.search("Claim (.*)\.([1-9][0-9]*):", claim)
        if mo:
            p_claim['name'] = mo.group(1)
            p_claim['num'] = mo.group(2)
            claim = claim[mo.end(0):]
            continue

        mo = re.search("[ \t]*file (.*) line ([1-9][0-9]*) function (.*)", claim)
        if mo:
            p_claim['file'] = mo.group(1)
            p_claim['line'] = mo.group(2)
            claim = claim[mo.end(0):]
            continue

#        print ">>>>>>"
#        print claim
#        print "========="
        break

    if (p_claim['name'] == None or p_claim['line'] == None or p_claim['num'] == None):
        print "cbmc Error:", p_claim
        return None

    return p_claim


################################################################################ 
# Get mapping from assertions to the claims reported by cbmc
#
def map_assertions_to_claims_cbmc(output_path, assertions, c2a):
    # Choose the correct executable for each platform
    if sys.platform == 'win32' or sys.platform == 'cygwin':
        cmd_str = ["cbmc.exe"]
    else:
        cmd_str = ["cbmc"]

    cmd_str.append("--show-claims")
    cmd_str.append(os.path.join(output_path, "a.out"))

#    print(" * Running: %s" % cmd_str)

    proc = subprocess.Popen(cmd_str, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env = os.environ)

    std_out, std_err = proc.communicate()
    std_out_str = std_out.decode("ascii")

    dump_output("__last_out", std_out_str)
    dump_output("__last_err", std_err.decode("ascii"))

    # Finished correctly?
#    if proc.returncode > 0:
#        print ("ERROR: Error during running cbmc")
#        exit(1)

    cbmc_claims = std_out.split("\n\n")[:-1]
    lines_to_claim = {}
    for claim in cbmc_claims:
        pc = parse_cbmc_claim(claim)
        if pc != None:
            f = pc['file']
            lnr = int(pc['line'])
            idx = search(lnr, assertions[os.path.basename(f)])
            cln = "%s.%s" % (pc['name'], pc['num'])
            if idx == -1:
                assert(False)
            else:
                assertions[os.path.basename(f)][idx].claim_nr = cln
                c2a[cln] = assertions[os.path.basename(f)][idx]

            lines_to_claim[pc['line']] = ["%s.%s" % (pc['name'], pc['num'])]

#################################################################################
# Performs a repeated check
#
def check_all_assertions_bot (check_type, orig_gb, files, input_path, output_path, assertions, claim2asrt):
    # Start working through the assertions one by one until all have been checked
    for f in assertions:
        print("File %s contains %d assertions" % (f, len(assertions[f])))
        for a in assertions[f]:

            if USE_CBMC:
                run_cbmc_single(check_type, orig_gb, output_path, "a.out", a, assertions, claim2asrt)
            else:
                run_evolcheck_single(check_type, orig_gb, output_path, "a.out", a, assertions, claim2asrt)

    if count_assertions(files, assertions, AssertionStates.Valid) == 0:
        print("All assertions are invalid.")
        return False

    print("  Unknown: %d" % count_assertions(files, assertions, AssertionStates.Unknown))
    print("  Invalid: %d" % count_assertions(files, assertions, AssertionStates.Invalid))
    print("  Valid: %d" % count_assertions(files, assertions, AssertionStates.Valid))
    return True


################################################################################ 
# Parses an assertion file
def parse_assertions (assertion_file, assertion_map, assertion_type):
    input_file = open(assertion_file, 'r');
    line = input_file.readline()

    while line:
        arr = line.split('\t',3)
        if len(arr) == 3:
            filename = arr[0]
            line_number = int(arr[1])
            expr = arr[2].strip()
#            print ('Assertion: file=%s, line=%s, expression="%s"' % (filename, line_number, expr))
            if not assertion_map.__contains__(filename):
                assertion_map[filename] = []

            assertion = Assertion(line_number, expr, assertion_type, AssertionStates.Unknown, filename)
            assertion_map[filename].append(assertion)
        else:
            print ('ERROR: unexpected line in the assertions file "%s"' % line)
        line = input_file.readline()
    input_file.close()



################################################################################ 
# A standard ends_with function known from the civilized world
#
def dump_output(file, text):
    output_file = open(file, 'w');
    output_file.write(text)
    output_file.close()



################################################################################ 
# A standard ends_with function known from the civilized world
#
def dump_trusted_assertions(assertions, files, file):
    output_file = open(file, 'w');

    for file in files:
        for assertion in assertions[file]:
            if assertion.state == AssertionStates.Valid:
                output_file.write("%s\t%d\t%s\n" % (file, assertion.src_line,
                    assertion.expression))

    output_file.close()



################################################################################ 
# A standard ends_with function known from the civilized world
#
def ends_with(string, pattern):
    return string.rfind(pattern) == len(string) - len(pattern)


################################################################################ 
# --- ENTRY ---
#

if __name__ == '__main__':
    # Check parameters
    if len(sys.argv) < 6 or (sys.argv[1] == "--upgrade-check" and len(sys.argv) < 8) or (sys.argv[1] != "--initial-check" and sys.argv[1] != "--upgrade-check"):
        print ("Expected at least 5 arguments")
        print ("")
        print ("Usage")
        print ("-----")
        print ("Initial check:")
        print ("> naive-hybrid-check.py --initial-check [untrusted_assertion_file] [input_path] [tmp_path] [file1] [file2] ...")
        print ("")
        print ("Upgrade check:")
        print ("> naive-hybrid-check.py --upgrade-check [orig_goto_binary] [trusted_assertion_file] [untrusted_assertion_file] [input_path] [tmp_path] [file1] [file2] ...")
        sys.exit(1)


    # Maps file names to the oredered lists of assertions (line,expression,type,state)
    assertion_map = {}

    # Input files with assertions and the paths
    if sys.argv[1] == "--initial-check":
        check_type = CheckTypes.Initial
        orig_gb = None
        untrusted_assertions_file = sys.argv[2]
        input_path = sys.argv[3] + ("" if ends_with(sys.argv[3], os.sep) else os.sep)
        output_path = sys.argv[4] + ("" if ends_with(sys.argv[4], os.sep) else os.sep)
        files = sys.argv[5:]
    elif sys.argv[1] == "--upgrade-check":
        check_type = CheckTypes.Upgrade
        orig_gb = sys.argv[2]
        trusted_assertions_file = sys.argv[3]
        untrusted_assertions_file = sys.argv[4]
        input_path = sys.argv[5] + ("" if ends_with(sys.argv[5], os.sep) else os.sep)
        output_path = sys.argv[6] + ("" if ends_with(sys.argv[6], os.sep) else os.sep)
        files = sys.argv[7:]


    # Parse the file with trusted and untrusted assertions
    parse_assertions(untrusted_assertions_file, assertion_map, AssertionTypes.Untrusted)
    if check_type == CheckTypes.Upgrade:
        parse_assertions(trusted_assertions_file, assertion_map, AssertionTypes.Trusted)

    # build the models
    process_files(files, input_path, output_path, assertion_map, False)

    claim_to_asrt = {}
    cbmc = False
    if USE_CBMC:
        map_assertions_to_claims_cbmc(output_path, assertion_map, claim_to_asrt)
    else:
        map_assertions_to_claims(output_path, assertion_map, claim_to_asrt)

    if check_type == CheckTypes.Initial:
        # Perform the check
        result = check_all_assertions_bot(check_type, orig_gb, files, input_path, output_path, assertion_map, claim_to_asrt)

        if result:
            dump_trusted_assertions(assertion_map, files, "__trusted")

        valid_asrts = []
        for file in assertion_map:
            for a in assertion_map[file]:
                if a.state == AssertionStates.Valid and a.summarizable:
                    valid_asrts.append(a)
        if not USE_CBMC:
            if len(valid_asrts) > 0:
                print("Generating the source file containing only valid assertions")
                process_files(files, input_path, output_path, assertion_map, True)
                print("Running check on the %d valid assertions to obtain summary." % len(valid_asrts))
                result = run_evolcheck_asrtset(check_type, orig_gb, output_path, "a.out", assertion_map, valid_asrts, claim_to_asrt)
                assert (result == True)
            else:
                print("No summarizable valid assertions found, skipping summarization")

    else:
        check_all_assertions(check_type, orig_gb, files, input_path, output_path, assertion_map, claim_to_asrt)

    print (' * Done.')

