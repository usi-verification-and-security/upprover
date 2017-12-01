int calculate_output();

int a0 = 0;

int calculate_output() {
    if (a0 == 0)
        a0 = 5;
    else if (a0 == 5)
        assert(0);
}

int main()
{
    while(1){
        calculate_output();
    }
}

//for unwind 2 should be SAT
