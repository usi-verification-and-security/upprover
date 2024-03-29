#include "constants.h"

static u_int
encode_ie(void *buf, size_t bufsize,                  // 8-byte character array
               const u_int8_t *ie, size_t ielen,          // 8-byte uint array
	       const char *leader, size_t leader_len)
{
  /* buf is treated as an array of unsigned 8-byte ints */
  u_int8_t *p;
  int i;

  // copy the contents of leader into buf
  if (bufsize < leader_len)
    return 0;
  p = buf;
  memcpy(p, leader, leader_len);
  bufsize -= leader_len;
  p += leader_len;

  /* This is the fix. */
  if (bufsize < ielen)
    return 0;

  for (i = 0; i < ielen && bufsize > 2; i++) {
    /* This was originally
     *    p += sprintf(p, "%02x", ie[i]);
     * This would print two digits from ie[i] into p, and 
     * return the number of bytes written.
     *
     * Simplified to remove sprintf.
     *
     */
    /* OK */
    *p = 'x';
    /* OK. */
__TESTCLAIM_1:
    *(p+1) = 'x';
    p += 2;
  }

  // if we wrote all of ie[], say how many bytes written in total, 
  // otherwise, claim we wrote nothing
  return (i == ielen ? p - (u_int8_t *)buf : 0);
}

int main()
{
  u_int8_t buf [BUFSZ];
  u_int8_t ie [IESZ];
  char leader [LEADERSZ];

  u_int res = encode_ie (buf, BUFSZ,
             ie, IESZ,
             leader, LEADERSZ);
  assert (res == 0);
  return 0;
}
