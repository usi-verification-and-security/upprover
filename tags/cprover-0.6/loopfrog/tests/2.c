void main(void)
{
  int a=5;
  char str[5];
  str[a-1]='\0';
  unsigned int i=0;
  while(str[i]!='\0')
    i++;
  assert(i<6);
}
