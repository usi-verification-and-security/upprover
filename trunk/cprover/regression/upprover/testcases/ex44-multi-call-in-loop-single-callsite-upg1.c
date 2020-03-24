unsigned int nondetUInt();

int sum (int w , int z)
{
    int s = 0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    for (int i = 0; i <2; i++)
    {
      z--;
   	  s = s + n + w ;
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
      a = sum(a , b);
      a = a-3;
      a = sum(a , b);
      assert(a >= 0);
    }
}

//sum has two entries in omega
//Total functions : 6
/*
__omega
sum
24
1
1
0
0
0
nondetUInt
28
2
1
0
0
-
sum
44
1
1
0
0
1,0

*/