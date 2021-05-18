short nondet_short();

int main(){
    short x = nondet_short();
    int y = 100000000;
    assert(y > x);
}
