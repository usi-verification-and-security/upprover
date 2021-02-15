void main()
{
    int i = nondet();
    int c = 0;
    if (i > 0 )
    	c = c + 2;
    else 
    	c = 4;

    assert(c > 3); //fail prop, lra
}