int a[4]; //array with a size of 4

void f()
{
	a[2] = a[1];
	a[3] = a[2];
	a[1] = a[3] + 1;
}


int main()
{
    f ();
 
    assert (a[2] == a[3]); // we have UF summary

   
    assert (a[1] > a[2]);
}
