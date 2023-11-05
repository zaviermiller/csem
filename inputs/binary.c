#ifdef DEFAULT_CLANG
int print(const char *fmt, ...);
#endif

int main() {
  int a, b, c, d;

  a = 1;
  b |= a;
  c = ~b + 2;
  d = -c;

  print("%d, %d, %d, %d", a, b, c, d);

  return 0;
}
