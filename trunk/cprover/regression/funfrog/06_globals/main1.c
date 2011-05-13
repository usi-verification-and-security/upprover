#define SIZE 256
#define EOF -1
#define ERROR -1

int nondet_int(); 

int XXX;

int getchar() {
  int x = nondet_int(); 

  XXX = 15;

  __CPROVER_assume(x <= 255);
  __CPROVER_assume(x >= -1);
  return x;
}

int choice(int a, int b) {
    if (a < 0 || a >= SIZE)
        return ERROR;
    if (b < 0 || b >= SIZE)
        return ERROR;

    int av = getchar();
    int bv = getchar();

    if (av >= bv)
        return a;
    return b;
}


int main() {
    int x, y, t;

    x = getchar();
    y = getchar();

    if (x == EOF || y == EOF)
        return 0;

    t = choice(x, y);
    assert (t == x || t == y);
}
