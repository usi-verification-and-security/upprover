int main()
{
   int a;
   
   __CPROVER_assume(a != 0);

   if (a > 0) 
   {
      a--;
   } else {
      a++;
   }

   assert(a != 0);
}

