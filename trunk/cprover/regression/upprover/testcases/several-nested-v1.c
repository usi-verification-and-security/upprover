unsigned int nondetUInt();

int glob_a;
int glob_b;

int getchar() {
  glob_b = nondetUInt(); 
  __CPROVER_assume(glob_b < 100);
  __CPROVER_assume(glob_b > 0);
  return glob_b;
}

void dec(){
  glob_a--;
}

void add(){
  glob_a++;
}

void change(){
  dec();
  add();
}

int c (int n){
return n+1;
}

int b(int n){
int m=c(n);
//assert(m>0);
return m+1;
}

int a(int n) {
int k=b(n+1);
//assert(k>0);
return k+1;
}

int hunc(int m){
    return 2 * m;
}
int gunc(int k){
    return k + 3 ;
}

int func ()
{
    int w, s=0;
    
    unsigned n = nondetUInt();
    __CPROVER_assume(n>0);
    __CPROVER_assume(n<10);

    s = s + n;
    w = gunc(s);
    return w;
}



void main(){
int n=1;
int m=a(n);
//int m2=b(n);
assert(m>0);

int a;

a=func();

a = hunc (a);

assert( a>= 5);

  glob_a = getchar();
  glob_b = glob_a;

  change();
  assert(glob_a == glob_b);

}


/*

  main 	     \		\
|		\	   \	 change
a    func      hunc 	add dec
|		  \		
b	 gunc		
|
c

*/
