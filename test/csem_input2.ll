; ModuleID = '<stdin>'
source_filename = "<stdin>"

declare i32 @print(ptr, ...)

define i32 @main() {
  %a = alloca i32, align 4
  %c = alloca i32, align 4
  %b = alloca double, align 8
  %d = alloca double, align 8
  %1 = load i32, ptr %a, align 4
  %2 = load double, ptr %b, align 8
  %3 = load i32, ptr %c, align 4
  %4 = load double, ptr %d, align 8
  ret i32 0
}
