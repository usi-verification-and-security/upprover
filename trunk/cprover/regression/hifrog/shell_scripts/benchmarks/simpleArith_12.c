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
   
   while (1==1) 
   {
     a = get2zero_test(a);
     assert(a != 0);
   }
}

