#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define SIZE		30

#define CAP		0
#define CUP		1
#define CAPF		2

int n;

// maps 1 <= a < b < c to 1 <= o(a,b,c)
int orient (int a, int b, int c) {
  assert (a < b);
  assert (b < c);
  return a + (b-2)*(b-1)/2 + (c-3)*(c-2)*(c-1)/6;
}

// maps 1 <= a < b < c to aux <= def(a,b,c,{CAP,CUP,CAPF},aux)
int def (int a, int b, int c, int d, int aux) {
  assert (a < b);
  assert (b < c);

  int size = 3;

  int rel = a + (b-2)*(b-1)/2 + (c-3)*(c-2)*(c-1)/6;
  return aux + size*rel + d;
}

int inside (int x, int a, int b, int c) {
  assert (a <  b);
  assert (b <  c);
  assert (a <  x);
  assert (x <  c);
  assert (x != b);

  int l = x, r = b;
  if (l > r) { l = b; r = x; }

  int base = n * (n-1) * (n-2) / 6;
  int more = 2 * (a + (l-2)*(l-1)/2 + (r-3)*(r-2)*(r-1)/6 + (c-4)*(c-3)*(c-2)*(c-1)/24) + -1 * (x < b);

  return base + more;
}

int hole (int a, int b, int c) {
  assert (a < b);
  assert (b < c);

  int base = n * (n-1) * (n-2) / 6 + n * (n-1) * (n-2) * (n-3) / 12;

  return base + a + (b-2)*(b-1)/2 + (c-3)*(c-2)*(c-1)/6;
}

void printInside (int d, int t, int i, int j) {
  printf ("%i %i %i 0\n", -d,  t, -i);
  printf ("%i %i %i 0\n", -d,  t, -j);
  printf ("%i %i %i 0\n", -d, -t,  i);
  printf ("%i %i %i 0\n", -d, -t,  j);
}
// d -> i = j = t

void defineInsideA (int x, int a, int b, int c) {
  assert (a < x);
  assert (x < b);
  assert (b < c);

  int d = inside (x, a, b, c);
  int t = orient (a, b, c);
  int axb = -orient (a, x, b);
  int axc =  orient (a, x, c);

  printInside (d, t, axb, axc);
}
// inside(x,a,b,c) -> orient(a,b,c) = -orient(a,x,b) = orient(a,x,c)

void defineInsideB (int x, int a, int b, int c) {
  assert (a < b);
  assert (b < x);
  assert (x < c);

  int d = inside (x, a, b, c);
  int t = orient (a, b, c);
  int axc =  orient (a, x, c);
  int bxc = -orient (b, x, c);

  printInside (d, t, axc, bxc);
}
// inside(x,a,b,c) -> orient(a,b,c) = orient(a,x,c) = -orient(b,x,c)

int main (int argc, char** argv) {
  n = SIZE;

  if (argc > 1)
    n = atoi (argv[1]);

  int nVar = n * (n-1) * (n-2) / 6;              // base variables
  nVar += n * (n-1) * (n-2) * (n-3) / 12;        // inside variables
  nVar += n * (n-1) * (n-2) / 6;                 // hole variables
  int nCls = (n-1) * (n-2) * (n-3) * (n-4) / 12; // axiom clauses
  for (int a = 2; a <= n; a++)
    for (int c = a+2; c <= n; c++)
      for (int d = c+1; d <= n; d++) nCls += 2;  // axiom clauses
  nCls += (n-1) * (n-2) * (n-3) * (n-4) / 3;     // inside clauses wo blocked
  nCls += (n-1) * (n-2) * (n-3) / 6;             // hole clauses wo blocked
  nCls += (n-1) * (n-2) / 2;                     // unit clauses
  nCls += 1 << ((n-3)/2);
  nCls--;

  int size = 3;
  nVar += size * n * (n-1) * (n-2) / 6;

  for (int a = 2; a <= n; a++)
    for (int b = a+1; b <= n; b++)
      for (int c = b+1; c <= n; c++)
        for (int d = c+1; d <= n; d++) {
          nCls += 2;
          if (b < a+2) continue;
          nCls += 2;
          if (b < a+3) continue;
          nCls += 1;
        }

  for (int a = 2; a <= n; a++)
    for (int c = a+2; c <= n; c++)
      for (int b = a+1; b < c; b++)
        for (int p = a+1; p < c; p++) {
          if (b == p) continue; // prevents BVA to do the optimization
          if ((b >= a+2) && (p >= a+2)) nCls++;
          if (b < a+3) continue;
          nCls += 1;
        }

  printf ("p cnf %i %i\n", nVar, nCls);

  // symmetry breaking predicate
  for (int a = 2; a <= n; a++)
    for (int b = a+1; b <= n; b++)
      printf ("%i 0\n", orient (1, a, b));

  // could be implemented without the arrays
  int reflect = (n-3)/2;
  int* midl = (int *) malloc (sizeof(int) * reflect);
  int* midr = (int *) malloc (sizeof(int) * reflect);
  for (int i = 0; i < reflect; i++) {
    midl[reflect-i-1] =  orient (  2+i,  3+i,4+i);
    midr[reflect-i-1] = -orient (n-2-i,n-1-i,n-i); }

  for (int i = 0; i < reflect; i++)
    for (int j = 0; j < (1 << i); j++) {
      for (int k = 0; k < i; k++)
        if ((1<<k) & j) printf ("%i ", midl[k]);
        else            printf ("%i ", midr[k]);
      printf ("%i %i 0\n", midl[i], midr[i]); }

  free (midl);
  free (midr);

  // single sign swap clauses
  for (int a = 2; a <= n; a++)
    for (int b = a + 1; b <= n; b++)
      for (int c = b + 1; c <= n; c++)
        for (int d = c + 1; d <= n; d++) {
          printf ("%i %i %i 0\n",  orient (a, b, c), -orient (a, b, d),  orient (a, c, d)); // P1
          printf ("%i %i %i 0\n", -orient (a, b, c),  orient (a, b, d), -orient (a, c, d)); // P2
        }
  // define inside variables
  for (int a = 2; a <= n; a++)
    for (int b = a+1; b <= n; b++)
      for (int c = b+1; c <= n; c++)
       for (int d = c+1; d <= n; d++) {
          defineInsideA (b, a, c, d);
          defineInsideB (c, a, b, d); }

  // define hole variables
  for (int a = 2; a <= n; a++)
    for (int b = a+1; b <= n; b++)
      for (int c = b+1; c <= n; c++) {
        printf ("%i ", hole (a, b, c));
        for (int x = a+1; x < c; x++)
          if (x != b) printf ("%i ", inside (x, a, b, c));
        printf ("0\n"); }

  int aux = 1 + n * (n-1) * (n-2) / 6;
  aux += n * (n-1) * (n-2) * (n-3) / 12; // inside variables
  aux += n * (n-1) * (n-2) / 6;          // hole variables

  for (int a = 2; a <= n; a++)
    for (int b = a+1; b <= n; b++)
      for (int c = b+1; c <= n; c++)
        for (int d = c+1; d <= n; d++) {
          printf ("%i %i %i 0\n",       def (a,c,d,CAP ,aux),  orient (a,b,c),  orient (b,c,d));
          printf ("%i %i %i 0\n",       def (a,c,d,CUP ,aux), -orient (a,b,c), -orient (b,c,d));
          if (b < a+2) continue;
          printf ("%i ", -hole (a,b,d));
          printf ("%i %i %i 0\n",       def (a,c,d,CAPF,aux),  orient (b,c,d), -def (a,b,c,CAP ,aux));
          printf ("%i ", -hole (a,b,d));
          printf ("%i %i 0\n",         -def (a,b,c,CUP ,aux), -orient (b,c,d));  // three below
          if (b < a+3) continue;
          printf ("%i %i 0\n",         -def (a,b,c,CAPF,aux),  orient (b,c,d));  // four above
        }
        // -orient(a,b,c) /\ -orient(b,c,d) -> cap(a,c,d)
        // orient(a,b,c) /\ orient(b,c,d) -> cup(a,c,d)
        // a+1 < b  =>  hole(a,b,d) /\ -orient(b,c,d) /\ cap(a,b,c) -> capf(a,c,d)
        // a+1 < b  =>  hole(a,b,d) /\ -cup(a,b,c) -> capf(a,c,d)

  // efficiently express axioms
  for (int a = 2; a <= n; a++)
    for (int c = a+2; c <= n; c++)
      for (int d = c+1; d <= n; d++) {
        printf ("%i %i 0\n", -def (a,c,d,CAP,aux), -orient (a,c,d));
        printf ("%i %i 0\n", -def (a,c,d,CUP,aux),  orient (a,c,d)); }

  for (int a = 2; a <= n; a++)
    for (int c = a+2; c <= n; c++)
      for (int b = a+1; b < c; b++)
        for (int p = a+1; p < c; p++) {
          if (b == p) continue;
          if ((b >= a+2) && (p >= a+2)) {
            if (b < p) { printf ("%i ", -hole (a,b,p)); }
            else       { printf ("%i ", -hole (a,p,b)); }
            printf ("%i %i 0\n", -def (a,b,c,CUP ,aux), -def (a,p,c,CAP ,aux));   // two above, two below
          }
          if (b < a+3) continue;
          printf ("%i %i 0\n",   -def (a,b,c,CAPF,aux), -orient (a,p,c));         // three above, one below
       }
}

