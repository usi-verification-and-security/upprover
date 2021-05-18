int main()
{
  unsigned a;
  unsigned b;
  unsigned e, f;
//  if (a <= 0 || a >= 100) return;
//  if (b <= 0 || b >= 100) return;
  if (e <= 0 || e >= 10) return;
  if (f <= 0 || f >= 10) return;

  unsigned c = (((a % 2) + (b % 2))) % 2;
  unsigned c_p = (a + b) % 2;
  unsigned d = e*f*c;
  unsigned d_p = e*f*c_p;

  assert(d == d_p);
}
