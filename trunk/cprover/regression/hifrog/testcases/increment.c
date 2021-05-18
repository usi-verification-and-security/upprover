int x;

void f(){
    ++x;
}

void g(){
    ++x;
}

int main(){
    f();
    g();
    assert(x > 0);
    return 0;
}
