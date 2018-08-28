int nondet();

int main(){
    int x = nondet();
    int y = x + 1;
    assert(y > x);
}
