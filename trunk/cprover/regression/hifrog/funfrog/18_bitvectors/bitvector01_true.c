unsigned long get_int();

unsigned long get_shift(unsigned long a, unsigned long b, unsigned long c){
  if (b <= c) {
    return a;
  } else {
    return a  >> 1;
  }
}

void main(){
  unsigned long a = get_int();
  unsigned long b = get_int();
  unsigned long c = get_int();

  a &= 0xFFFFFFFFUL;
  b &= 0xFFFFFFFFUL;

  unsigned long d = get_shift(a, b, c);

  assert(a >= d);

}
