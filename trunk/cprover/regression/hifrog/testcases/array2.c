int f();
 
 int sum(int* a){
     return a[0] + a[1];
 }
 
 int main(){

     int y[3];    //the size of array is bounded to be 3     
     y[0] = 1;   
     y[1] = 2;
     int res = sum(y);    //pass the array to a function sum(), using a pointer to it

     assert(res == 3);

//the second part:

    int i=nondet();
     __CPROVER_assume(i > 5);
     __CPROVER_assume(i < 10);

    char x[i];  //the size of array is bounded to be between 5 and 10
    __CPROVER_assume(x[3] == 'a');
    assert(x[2] != 'y' || x[4] != 'z');

    assert(x[3] == 'a');
 }


