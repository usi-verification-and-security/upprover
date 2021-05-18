void f(int* x){
    *x = 0;
}

int main(){
    int a = 10;
    int* x = &a;
    f(x);
    assert(*x == 0);
    return 0;
}
