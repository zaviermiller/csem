#ifdef DEFAULT_CLANG
int print(const char *fmt, ...);
#endif

int main() {
  int i;
  for (i = 0; i < 12; i += 1)
    print("i: %d\n", i);
  return 0;
}
