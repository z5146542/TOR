
unsigned max(unsigned a, unsigned b) {
  if (a <= b)
    return b;
  return a;
}

void func(unsigned *p) {
  unsigned x = *p;
  if (x < 10) {
    *p = x + 1;
  }
}

unsigned gcd(unsigned a, unsigned b) {
  unsigned c;
  while (a != 0) {
    c = a;
    a = b % a;
    b = c;
  }
  return b;
}

unsigned except(unsigned u) {
  if (u >= 9)
    return 8;
  
  while (u < 9){
    if (u > 5)
      return u;
    if (u > 4)
      break;
    u++;
  }
  u++;
  return u;
}



