int sum(int w){
    return w+1;
}

int main(){
    int a;
    __CPROVER_assume(a>0);
    __CPROVER_assume(a<10);
      
      a=sum(a);
      a++;
      assert(a>=0);
      a=sum(a);
      a++;
      assert(a>=0);
}