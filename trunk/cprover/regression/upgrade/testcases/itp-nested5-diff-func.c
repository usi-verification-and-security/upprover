/*
if u run :
./hifrog --all-claims /Users/sepidehasadi/2phd/dev/bench/itp-test/itp-nested5-diff-func.c --logic qflra 

a summary will be generated for all the functions, now lets test it if those summaries are reusable??

*/
/*1st test: Not-reusable
  ./hifrog --claim 4 /Users/sepidehasadi/2phd/dev/bench/itp-test/itp-nested5-diff-func.c --logic qflra --load-summaries __summaries_all_claims_ex5
  it will hit the internal assert and gets aborted: Assertion failed: (symbols.size() == static_cast<std::size_t>(args.size())), function insert_substituted,
  file /Users/sepidehasadi/2phd/dev/hifrog2/hifrog/trunk/cprover/src/funfrog/solvers/smtcheck_opensmt2.cpp, line 649.  */
/* *************************
  2nd test: Not-reusable
  ./hifrog --claim 2 /Users/sepidehasadi/2phd/dev/bench/itp-test/itp-nested5-diff-func.c --logic qflra --load-summaries __summaries_all_claims_ex5 
*** SUMMARY abstraction used for function: a.    //why a?
*** INLINING function: b2
*** SUMMARY abstraction used for function: c2 */

int c2 (int n2){
	return n2+1;
}

int b2(int n){
 int m2=c2(n);
 assert(m2>0);   //claim 2
 return m2+1;
}

////////////

int c (int n){
 return n+1;
}

int b(int n){
 int m=c(n);
 assert(m>0);   //claim 3
 return m+1;
}

int a(int n) {
 int k=b(n+1);
 assert(k>0);   //claim 4
 return k+1;
}

void main(){
 int n=1;
 int m=a(n);
 int mm2=b2(n);
 //assert(m>0);
 assert(mm2 >= 3);  //claim 1
}


/*

main	
|---.
a	b2
|   :
b	c2
|
c	

*/
