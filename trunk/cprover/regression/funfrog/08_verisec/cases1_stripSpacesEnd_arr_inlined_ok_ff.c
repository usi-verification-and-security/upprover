#include "constants.h"

static int parse_expression_list(char *str) 
{
  int start=0, i=-1, j=-1;
  char str2[EXPRESSION_LENGTH];
	
  if (!str) return -1;

  do {

    /* i only changes here --> it's the "current character" */
    i++;
    switch(str[i]) {
    case EOS:	/* word found */

      /* Set j to point to the end of the current word */
      j = i-1;

      /* Skip over quotes and whitespace at the END of the word */
      while ((0 < j) && ((str[j] == ' '))) j--;

      /* If word not empty.... */
      if (start<=j) {
        /* valid word */
        if (j-start+1>=EXPRESSION_LENGTH) {
          return -1;
        }
        /* OK */
        //assert (j-start+1 < EXPRESSION_LENGTH);
        r_strncpy(str2, str+start, j-start+1);
        str2[j-start+1] = EOS;
      } else {
        /* parsing error */
        return -1;
      }
      /* for the next word */
      start = i+1;
    }
  } while (i <= LINE_LENGTH);// (str[i] != EOS); //-- matching within char[] elements doesn't work for some reason

  return i;
}


int main ()
{
  char A [LINE_LENGTH+1];
  A[LINE_LENGTH] = EOS;

  int r = parse_expression_list (A);
  assert(r == LINE_LENGTH+1 || r == -1);

//  assert(r == LINE_LENGTH+1 || r == -1); //--doesn't work

  return 0;
}
