int nondet();
int mod_Cd(int a, int n)
{
  int temp;
  if (a==n)
     temp = 0;
  
  return temp;
}
void main()
{
    int y = nondet();

    unsigned int z = mod(y,y);
    __CPROVER_assume(mod_Cd(y,y) == z);
    assert(z == 0);
}

