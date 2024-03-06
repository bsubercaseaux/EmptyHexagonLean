#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define SIZE		30
#define BITS		21

//#define ODD
//#define VALIDATE
#define SBP

#define OFFSET		0

#define MASKA		21
#define MASKB		31

int* varLookup = 0;

int lookup(int index) {
  return varLookup ? varLookup[index] : index;
}

unsigned int orient (int a, int b, int c) {
  assert (a < b);
  assert (b < c);

  return lookup(a + (b-2)*(b-1)/2 + (c-3)*(c-2)*(c-1)/6);
}

unsigned int invalid (unsigned int bv, unsigned int bits) {
  int full = (1 << bits) - 1;

  int pos = 7;
  for (int j = 0; j < bits; j++)
    if (((pos << j) & bv) == (pos << j))
      return pos << j;

  int neg = 15;
  for (int j = 0; j < bits; j++)
    if (((neg << j) & (bv^full)) == (neg << j))
      return neg << j;

  return 0;
}

unsigned int mirror (unsigned int bv, unsigned int bits) {
  int result = 0;
  for (int i = 0; i < bits; i++)
    if (bv & (1 << i))
      result |= 1 << (bits - i - 1);

  return result;
}

unsigned int lex (unsigned int bv, unsigned int bits) {
  int low  = (bits - 1) / 2;
  int high = (bits - 0) / 2;

  while (low >= 0) {
    int l = (bv & (1 << low )) > 0;
    int h = (bv & (1 << high)) > 0;
    if (l > h) return 0;
    if (l < h) return 1;
    low--; high++;
  }
  return 0;
}

// for debugging
void printMask (int bv, int bits) {
  for (int i = 0; i < bits; i++) {
    if ((1 << i) & bv) printf ("1");
    else               printf ("0"); }
}

void printCube (int *array, int size) {
#ifdef VALIDATE
  for (int i = 0; i < size; i++)
    printf ("%i ", -array[i]);
#else
  printf ("a ");
  for (int i = 0; i < size; i++)
    printf ("%i ", array[i]);
#endif
  printf ("0\n");
}

int main (int argc, char** argv) {
//  int n    = atoi (argv[1]);
//  int bits = atoi (argv[2]);

  int match = 0;
  if (argc > 1)
    match = atoi (argv[1]);
  int count = 1;

  int n    = SIZE;
  int bits = BITS;

  assert (bits < (n - 2));
  assert ((n & 1) != (bits & 1));

  int offset = (n - bits - 3) / 2;

  if (argc > 2) {
    int* p = (int*) malloc (sizeof (int) * (n * (n-1) * (n-2) / 6 + 1));
    FILE* ptr = fopen(argv[2], "r");
    if (ptr == NULL) {
      printf("file missing");
      return 1;
    }
    char buf[100];
    int ty, x, a, b, c, i = 1;
    while (fscanf(ptr, "%d %d %d %d %d ", &ty, &x, &a, &b, &c) == 5) {
      if (ty == 0)
        p[orient(a+1, b+1, c+1)] = i++;
    }
    varLookup = p;
  }

//  int offset = OFFSET;
//  if (argc > 2) offset = atoi (argv[2]);

  int *dudud, *cube, size;
  dudud = (int *) malloc (sizeof (int) * (2*bits+2*offset));
  cube  = (int *) malloc (sizeof (int) * (2*bits+2*offset));

  int max = (1 << bits) - 1;

#ifdef VALIDATE
  printf ("p cnf %i %i\n", orient (bits+1, bits+2, bits+3), 0);
#endif

  int f = 1;
#ifdef ODD
  f = 2;
#endif
  int palin = 0;
  for (int i = 0; i <= max; i++) {
    size = 0;

    if (invalid (i, bits)) continue;

    if (i == mirror (i,bits)) palin++;

#ifdef SBP
    if (lex (i, bits)) continue;
//    if (i > mirror (i, bits)) continue;
#endif
    unsigned int mask = max;

    int extra = 0;

    int j = i << 1;

    int c = 0;
    while (j) {
      if (((j ^ MASKA) & MASKB) == MASKB)
        dudud[extra++] = orient (c + offset + 1, c + offset + 3, c + offset + 5);
      j = j >> 1;
      c++;
    }

    for (int b = 0; b < bits; b++) {
      if (((1 << b) & mask) == 0) continue;
      if (((1 << b) & i   ) == 0)
        cube[size++] = -orient (f*b + offset + 2, f*b + offset + 3, f*b + offset + 4);
      else
        cube[size++] =  orient (f*b + offset + 2, f*b + offset + 3, f*b + offset + 4); }

//      extra = 0;
      int m = (1 << extra) - 1;
      for (int k = 0; k <= m; k++) {
        size = bits;
        for (int e = 0; e < extra; e++) {
          if (((1 << e) & k   ) == 0)
           cube[size++] = -dudud[e];
          else
           cube[size++] =  dudud[e]; }

        if (match == 0 || count == match)
          printCube (cube, size);
        count++;
      }
  }

#ifdef VALIDATE
  int reflect = (n-3)/2;
  int* midl = (int *) malloc (sizeof(int) * reflect);
  int* midr = (int *) malloc (sizeof(int) * reflect);
  for (int i = 0; i < reflect; i++) {
    midl[reflect-i-1] =  orient (  2+i,  3+i,4+i);
    midr[reflect-i-1] = -orient (n-2-i,n-1-i,n-i); }

  printf ("c symmetry-breaking predicate\n");

  for (int i = 0; i < reflect; i++)
    for (int j = 0; j < (1 << i); j++) {
      for (int k = 0; k < i; k++)
        if ((1<<k) & j) printf ("%i ", midl[k]);
        else            printf ("%i ", midr[k]);
      printf ("%i %i 0\n", midl[i], midr[i]); }

  free (midl);
  free (midr);

  printf ("c original clauses\n");

  int o = offset;
//  for (int i = 2; i+1 <= bits; i++)
  for (int i = 2; i+1 <= n; i++)
    printf ("%i %i %i 0\n", -orient (i, i+1, i+2), -orient (i+1, i+2, i+3), -orient (i+2, i+3, i+4));
//    printf ("%i %i %i 0\n", -orient (i+o, i+o+1, i+o+2), -orient (i+o+1, i+o+2, i+o+3), -orient (i+o+2, i+o+3, i+o+4));

//  for (int i = 2; i+2 <= bits; i++)
  for (int i = 2; i+2 <= n; i++)
    printf ("%i %i %i %i 0\n", orient (i, i+1, i+2), orient (i+1, i+2, i+3), orient (i+2, i+3, i+4), orient (i+3, i+4, i+5));
//    printf ("%i %i %i %i 0\n", orient (i+o, i+o+1, i+o+2), orient (i+o+1, i+o+2, i+o+3), orient (i+o+2, i+o+3, i+o+4), orient (i+o+3, i+o+4, i+o+5));
#endif

//  printf ("c palindromes: %i\n", palin);

}

