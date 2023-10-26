; ModuleID = '<stdin>'
source_filename = "<stdin>"

declare i32 @print(ptr, ...)

define i32 @main() {
  %a = alloca i32, align 4
  %c = alloca i32, align 4
  %b = alloca double, align 8
  %d = alloca double, align 8
  store i32 3, ptr %a, align 4
  store i32 4, ptr %b, align 4
  store i32 5, ptr %c, align 4
  store i32 6, ptr %d, align 4
  ret i32 0
}
