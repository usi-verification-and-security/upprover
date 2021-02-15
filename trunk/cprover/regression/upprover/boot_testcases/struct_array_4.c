#include <assert.h>
struct St {
  char c;
  int d[];
};
struct St s = {'a', {11, 5}};

int main () {
  unsigned char c;
  c = c && 1;
  assert(c==0 || c==1);
  assert(s.d[1]==5);
  s.d[1] += c;
  assert(s.d[1]<8);
  assert(s.d[0]==11);
}