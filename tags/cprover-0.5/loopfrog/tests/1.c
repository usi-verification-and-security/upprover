void main(void)
{
  int a=5;
  char str[5];
  str[a-1]='\0';
  int i=0;
  while(str[i]!='\0')
  {
    i+=1;
  }
  assert(i<6);
}
