int XXX;

int nondet_int(); 

int x(int a) {
    if (nondet_int()) {
      XXX = a;
      return a;
    } else {
      return XXX;
    }
}


int main() {
    int i,j;
    XXX = nondet_int();
    j = nondet_int();
    i = XXX;

    x (j);

    assert (i == XXX || j == XXX);
}
