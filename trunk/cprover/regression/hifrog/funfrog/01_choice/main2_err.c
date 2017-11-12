#define SIZE 256
#define EOF -1
#define ERROR -2

int lookup[SIZE];

int nondet_int(); 

int getchar(int z) {
  int x = nondet_int(); 

  __CPROVER_assume(x <= 255);
  __CPROVER_assume(x >= -1);
  return x;
}

int main() {
    int x, t;

    x = getchar(t);

    if (x == 1) {
      t = 1;
    } else if (x == 2) {
      t = 3;
    } else if (x == 3) {
      t = 5;
    } else if (x == -1) {
      t = ERROR;
    } else {
      t = 10;
    }

    assert (t != ERROR);
}
