#define SIZE 256
#define EOF -1
#define ERROR -1

int nondet_int();

int getchar() {
  int x = nondet_int();

  __CPROVER_assume(x <= 255);
  __CPROVER_assume(x >= -1);
  return x;
}

int choice(int a) {
    if (a < 0 || a >= SIZE)
        return ERROR;

    int av = getchar();
    return a;
}


int main() {
    int x, y, t;

    x = getchar();

    t = choice(x);
    assert (t == x); 
    //expected result for lra is SAT
    // claim 1 fails for LRA, because it's assumed there is no
    // integer between -1 and 0, while in LRA 
    // there is a Real between -1 and 0

}