int x = 0;

void inc(){
    ++x;
}

int main(){
    inc();
    assert(x > 0);
    return 0;
}
