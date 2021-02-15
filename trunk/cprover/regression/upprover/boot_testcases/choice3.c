#define SIZE 32
#define EOF -1
#define ERROR -1

int lookup[SIZE];

int nondet_int(); 

int getchar() {
  int x = nondet_int(); 

  __CPROVER_assume(x < SIZE);
  __CPROVER_assume(x >= -1);
  return x;
}

int choice(int a, int b) {
    if (a < 0 || a >= SIZE)
        return ERROR;
    if (b < 0 || b >= SIZE)
        return ERROR;

    int av = lookup[a];
    int bv = lookup[b];

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
