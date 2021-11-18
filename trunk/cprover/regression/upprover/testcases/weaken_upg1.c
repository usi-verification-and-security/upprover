int a,b,c,d;

f(){
  a = 0;
  // b = 1;
   b++; b--; //this is done to preserve b in summary args, 
             //otherwise pre-computed summary will not be matched
}

g(){
  c = 0;
}

h(){
  f();
  g();
  d = a + c;
}

main(){
  h();
  assert(d >= 0);
}

//   h
//  /\
//  f g
//s(f): (a>= 0)
//s(g):  c >= 0
//s(h):  (d>=0)