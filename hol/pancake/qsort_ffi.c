/*
  Trusted C glue for the Pancake quicksort.

  Implements exactly the FFI oracle `qs_oracle` that the HOL4 correctness
  theorem assumes (see panQsortScript.sml).  Numbers are 64-bit two's
  complement words, transferred little-endian (x64 byte order):

    get_num : array of 9 bytes.  If stdin has another integer n (scanf "%lld"):
                a[0..7] := n (little-endian), a[8] := 1
              otherwise (end of input or a non-number):
                a[0..8] := 0
    put_num : array of 8 bytes.  Prints the integer a[0..7] and a newline;
              the array is unchanged.

  It also allocates the Pancake heap and stack and starts the program.
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

static int input_done = 0;

void ffiget_num(unsigned char *c, long clen, unsigned char *a, long alen) {
  long long n;
  if (alen != 9) abort();
  if (!input_done && scanf("%lld", &n) == 1) {
    uint64_t u = (uint64_t) n;
    for (int i = 0; i < 8; i++) a[i] = (unsigned char) (u >> (8 * i));
    a[8] = 1;
  } else {
    input_done = 1;
    memset(a, 0, 9);
  }
}

void ffiput_num(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t u = 0;
  if (alen != 8) abort();
  for (int i = 0; i < 8; i++) u |= (uint64_t) a[i] << (8 * i);
  printf("%lld\n", (long long) u);
}

/* Called by the compiled code when it stops; exit() flushes stdout. */
void cml_exit(int arg) {
  if (arg != 0) fprintf(stderr, "Pancake program stopped with code %d (stack/heap limit?)\n", arg);
  exit(arg);
}

/* Referenced by the assembly stub; only used by CakeML's dynamic code
   installation, which compiled Pancake programs never perform. */
void *cml_install(uint8_t *src, size_t len, uint8_t *dest) { abort(); }

/* The empty-named FFI call is used for internal events and is a no-op. */
void ffi(unsigned char *c, long clen, unsigned char *a, long alen) { }

int main(int argc, char **argv) {
  unsigned long mb = 1024 * 1024;
  unsigned long heap_sz = 512 * mb, stack_sz = 256 * mb;
  char *h = getenv("CML_HEAP_SIZE"), *s = getenv("CML_STACK_SIZE");
  if (h) heap_sz = strtoul(h, NULL, 10) * mb;
  if (s) stack_sz = strtoul(s, NULL, 10) * mb;
  cml_heap = malloc(heap_sz + stack_sz);
  if (cml_heap == NULL) { fprintf(stderr, "malloc failed\n"); return 3; }
  cml_stack = (char *) cml_heap + heap_sz;
  cml_stackend = (char *) cml_stack + stack_sz;
  cml_main();
  return 0;
}
