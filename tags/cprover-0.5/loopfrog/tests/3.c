#include <stdlib.h>

void main(void)
{
  int a=5;
  char str[5];
  str[4]='\0';
  char *p;
  p=str;
  while(*p!='\0')
  {
    p++;
  }
  assert(p!=NULL);
}
