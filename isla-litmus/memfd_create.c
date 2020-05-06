
#define CAML_NAME_SPACE
#include <caml/mlvalues.h>
#include <caml/signals.h>
#include <caml/fail.h>

#include <sys/syscall.h>
#include <unistd.h>

CAMLprim value linux_memfd_create(value v)
{
  const char *file_name = String_val(v);
  caml_enter_blocking_section();
  int ret = syscall(SYS_memfd_create, file_name, 0);
  caml_leave_blocking_section();
  if (ret == -1) caml_failwith("memfd_create");
  return Val_int(ret);
}
