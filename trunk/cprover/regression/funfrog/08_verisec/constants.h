#ifndef _CONSTANTS_H
#define _CONSTANTS_H

#include "stubs.h"

#define EXPRESSION_LENGTH BASE_SZ
#define NEEDLE "EX"
#define NEEDLE_SZ 2

/* Enough to fill a buffer of size EXPRESSION_LENGTH, enough to
 * contain the needle, and enough to overflow the buffer. */
#define LINE_LENGTH EXPRESSION_LENGTH + NEEDLE_SZ + 4

typedef unsigned int u_int;
typedef unsigned char u_int8_t;

struct ieee80211_scan_entry {
  u_int8_t *se_rsn_ie;            /* captured RSN ie */
};

#define IEEE80211_ELEMID_RSN 200 /* fake */

/* Size of an array leader[] which is written to buf[] before it is
 * overflowed by the ie[] array. */
#define LEADERSZ 1

/* We first write the "leader" to buf[], and then write from the "ie"
 * array. buf[] has to be bigger than LEADERSZ by at least 2. */
#define BUFSZ BASE_SZ + LEADERSZ + 2

/* Just has to be big enough to overflow buf[] */
#define IESZ (BUFSZ - LEADERSZ) + 5


#endif
