#ifdef DEFAULT_CLANG
int print(const char *fmt, ...);
#endif
int main() {
  if (1 == 1) {
    print("hey\n");
  } else {
    print("yo\n");
  }

  return 0;
}
