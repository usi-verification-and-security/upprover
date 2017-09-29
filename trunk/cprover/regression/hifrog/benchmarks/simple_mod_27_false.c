void main() 
{
  int n, res_mod;
  while (1==1) 
  {
     __CPROVER_assume(n != 0); 
     res_mod = res_mod % n; 
     __CPROVER_assume(res_mod != 0);

     assert(res_mod > n); 
  }
}
