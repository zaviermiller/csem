#ifdef DEFAULT_CLANG
int print(const char *fmt, ...);
#endif
int main() {
  int a, b;

  a = 1;
  b = 1;
  if (a == b) {
    print("hey\n");
  } else {
    print("yo\n");
  }

  return 0;
}
