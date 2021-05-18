#include <assert.h>
struct St {
  int d[];
};
struct St s = {{5}};

int main () {

  s.d[0] = 1;
  assert(s.d[0]<8);
}
