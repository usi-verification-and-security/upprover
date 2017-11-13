extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;    
}
/* https://graphics.stanford.edu/~seander/bithacks.html#InterleaveTableObvious */
#include <assert.h>

    unsigned int z;

int main()
{
    /* Interleave bits of x and y, so that all of the */
    /* bits of x are in the even positions and y in the odd; */
    unsigned short x;
    unsigned short y;

    unsigned int xx;
    unsigned int yy;
    unsigned int zz;

    unsigned int C;

    z = 0; /* z gets the resulting Morton Number. */
    unsigned int i = 0;

    while (i < 32U) {
        z |= ((x & (1U << i)) << i) | ((y & (1U << i)) << (i + 1));
        i += 1U;
    }

    xx = x;
    yy = y;

    xx = (xx | (xx << 8u)) & 16711935U; /* 0x00FF00FF */
    xx = (xx | (xx << 4u)) & 252645135U; /* 0x0F0F0F0F */
    xx = (xx | (xx << 2u)) & 858993459U; /* 0x33333333 */
    xx = (xx | (xx << 1u)) & 1431655765U; /* 0x55555555 */
        
    yy = (yy | (yy << 8u)) & 16711935U; /* 0x00FF00FF */
    yy = (yy | (yy << 4u)) & 252645135U; /* 0x0F0F0F0F */
    yy = (yy | (yy << 2u)) & 858993459U; /* 0x33333333 */
    yy = (yy | (yy << 1u)) & 1431655765U; /* 0x55555555 */
    
    zz = xx | (yy << 1U);
    if (C == 6U) assert(z == zz || zz > 1000U || z <= 0U);
    //if (C == 9U) assert(z == zz || zz > 1000U || z <= 0U);
    //if (C == 12U) assert(z == zz || zz > 1000U || z <= 0U);
    //if (C == 15U) assert(z == zz || zz > 1000U || z <= 0U);
    //if (C == 18U) assert(z == zz || zz > 1000U || z <= 0U);
    //if (C == 21U) assert(z == zz || zz > 1000U || z <= 0U);
    //if (C == 24U) assert(z == zz || zz > 1000U || z <= 0U);
    //if (C == 27U) assert(z == zz || zz > 1000U || z <= 0U);
    //if (C == 30U) assert(z == zz || zz > 1000U || z <= 0U);
   // if (C == 32U) assert(z == zz || zz > 1000U || z <= 0U);
}
