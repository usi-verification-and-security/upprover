struct S{
    int x;
    int y;
};

struct S s;

int sum(){
    return s.x + s.y;
}

int main(){
    s.x = 1;
    s.y = 2;
    int r = sum();
    assert(r > 0);
    return 0;
}
