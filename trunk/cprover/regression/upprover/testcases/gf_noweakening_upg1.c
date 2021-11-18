int a,b,c,d;

f(){
  a = 1;
  b = -1;
}

g(){
  c = 1;
}

h(){
  f();
  g();
  d = a + b + c;
}

main(){
  h();
  assert(d >= 1);
}


