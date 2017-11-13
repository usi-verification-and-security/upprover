#define SIZE 256
#define EOF -1
#define ERROR -1

int lookup[SIZE];

int nondet_int(); 

int getchar() {
  int x = nondet_int(); 

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

//    if (x == EOF || y == EOF)
//        return 0;

    t = choice(x, y);
    assert (t == x || t == y);

//    t = choice(1, 1);
//    assert (t == 1);

//    t = choice(10, 20);
//    assert (t >= 10 || t <= 20);
//    assert (t == 20);

//    t = choice(-1, -1);
//    assert (t == ERROR);
}
