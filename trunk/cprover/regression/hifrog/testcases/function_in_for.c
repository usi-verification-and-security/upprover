int f(int a){
    if(a > 0)
        a =  0;
    else
        a = 1;
    return a;
}

int main(){
    int x = 0;
    for(int i = 0; i < 3; ++i){
        x = f(x);
    }
    assert(x > 0);
}
