unsigned int nondetUInt();

int plusTwo(int k){
	return k + 2 ;
}

int sum (int bb)
{
    int s = 0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    s = plusTwo(bb);
    s = s + n;
    return s;
}

int main()
{
    int a, b = 5;

    a = sum(b);
    assert( a >= 0);

}

