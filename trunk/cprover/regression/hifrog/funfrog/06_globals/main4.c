int XXX;

int nondet_int(); 

void x(int a) {
  if (nondet_int())
    XXX = a;
  else
    XXX = XXX;
}


int main() {
    int i,j;
    XXX = nondet_int();
    j = nondet_int();
    i = XXX;

    x (j);

    assert (i == XXX || j == XXX);
}
