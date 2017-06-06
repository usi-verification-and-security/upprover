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

 a0 = calculate_output(a0);
 a0 = calculate_output(a0);
}

//for unwind 2 should be SAT
