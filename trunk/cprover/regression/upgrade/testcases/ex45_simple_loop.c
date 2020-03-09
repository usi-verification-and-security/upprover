int sum(int w){
    return w+1;
}

int main(){
    int a;
    __CPROVER_assume(a>0);
    __CPROVER_assume(a<10);
    for (int i = 0; i < 2; ++i){
      a=sum(a);
      a++;
      assert(a>=0);
    }
}