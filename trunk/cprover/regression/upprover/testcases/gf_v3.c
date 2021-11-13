int a,b,c,d;

f(){
  a = 0;
  b = 0;
}

g(){
  c = 0;
}

h(){
  f();
  g();
  d = a + b + c;
}

main(){
  h();
  assert(d >= 0);
}


//sum(g):c>=0
//sum(d): d>=0
//sum(f):a>=0 /\ b>=0 
//TI hold: a>=0 /\ b>=0 /\ c>=0 /\ d=a+b+c -->d>=0