int nondet_bool();

int get_int(){
  int g = nondet_bool();
  __CPROVER_assume (g == 0 || g == 1);
  return g;
}

int a;
int i;

void loop(){
  int b = get_int();
  if (b == 0 || a == 1){
    i--;
    loop();
  }
  i++;
}


void main (void){
  i = 0;

  loop();

  assert (0);
}
