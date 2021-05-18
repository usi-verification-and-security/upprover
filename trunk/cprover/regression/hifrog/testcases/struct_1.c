struct S{
    int x;
    int y;
};

struct S s;

f(){
    s.x = 0;
}

int main(){
    s.x = 1;
    s.y = 2;
    f();
    assert(s.x == 0);
    return 0;
}
