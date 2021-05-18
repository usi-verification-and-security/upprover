int get2zero_test(int a)
{
   if (a > 0) 
   {
      a--;
   } else {
      a++;
   }

   return a;
}

int main()
{
   int a;
   
   __CPROVER_assume(a != 0);
   a = get2zero_test(a);

   assert(a != 0);
}

