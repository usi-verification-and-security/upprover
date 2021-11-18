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

//   h
//  /\
//  f g
//s(f): (a>= 0) and (b >= 0)
//s(g):  c >= 0
//s(h):  (d>=0)