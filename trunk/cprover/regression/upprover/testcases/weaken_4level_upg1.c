int a,b,c,d;

f(){
  a = 1;
  b = -1;
}

g(){
  c = 0;
}

h(){
  f();
  g();
  d = a + b + c;
}

void call() {
  h();
  d++;
}

main(){
  call();
  assert(d >= 0);
}


//sum(g):c>=0
//sum(d): d>=0
//sum1^w(f):a>=0  
//TI does not hold: a>=0 /\ c>=0 /\ d=a+b+c -->d>=0
//TI holds by refinement a=1 /\ b=-1 /\ a>=0 /\c>=0 /\ d=a+b+c -->d>=0
//sum2^i(f):a>=1 /\ b>=-1 by DEc Far
//sum2^i(f):a+b>=0 by DEc Far
//sum(f)=sum1^w(f) /\ sum2^i(f)