/* strncpy example */
//#include <stdio.h>
//#include <string.h>
#define LEN 2

char *strncpy (char *dest, const char *src, int n) {
  for (int i = 0; i < n; ++i) {
    *dest = *src;
    if (!*src)
      return dest;
    ++dest;
    ++src;
  }
  return dest;
}

int main ()
{
  char str1[]= "To be ";
  char str2[LEN];
  strncpy (str2,str1,LEN-1);

  assert('T' == str1[0]);

  //puts (str2);
  return 0;
}
