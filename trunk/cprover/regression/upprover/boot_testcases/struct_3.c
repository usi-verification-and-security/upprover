struct tiny {
    char field;
};

int main()
{
    struct tiny x;
    assert(x.field == 0);
}