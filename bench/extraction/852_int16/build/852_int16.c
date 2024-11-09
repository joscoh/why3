#include <stdint.h>


uint16_t bcd_compute(uint16_t src) {
  uint16_t dig1, r1, dig2, r2, dig3, dig4;
  dig1 = src / 1000u;
  r1 = src % 1000u;
  dig2 = r1 / 100u;
  r2 = r1 % 100u;
  dig3 = r2 / 10u;
  dig4 = r2 % 10u;
  return dig1 * 4096u + dig2 * 256u + dig3 * 16u + dig4;
}
