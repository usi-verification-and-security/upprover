unsigned get_int();

void main(){
  unsigned a = get_int();
  unsigned b = get_int();
  unsigned c = get_int();
  unsigned d = get_int();

  a &= d; a |= 1U;
  b &= d; b |= 1U;

  unsigned e = a >> 1;

  assert((e^a) != 0u); 
}
