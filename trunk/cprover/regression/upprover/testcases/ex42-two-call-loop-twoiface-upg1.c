unsigned int nondetUInt();

int sum (int w , int z)
{
    int s = 0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    for (int i = 0; i <2; i++)
    {
      z++;
   	  s = s + n + w + 1;
    }
    return s;
}

int main(){
    int a , b;
    __CPROVER_assume(a>0);
    __CPROVER_assume(a<30);
    __CPROVER_assume(b>0);
    __CPROVER_assume(b<30);
    for (int i = 0; i < 2; ++i)
    {
      if(i == 0){
        a = sum(a , b);
      }
      a++;
      if(i == 1){
        a = a-3;
        a = sum(a , b);
      }
      assert(a >= 0);
    }
}

//sum has two entries in omega
//Total functions : 6