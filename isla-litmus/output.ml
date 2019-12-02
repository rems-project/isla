open Printf

let opt_colors = ref true
let opt_verbosity = ref 0

let termcode n =
  if !opt_colors then
    "\x1B[" ^ string_of_int n ^ "m"
  else ""

let red str = termcode 91 ^ str
let yellow str = termcode 93 ^ str
let clear str = str ^ termcode 0

let log_start_time : float ref = ref (Sys.time ())

let fatal str =
  eprintf "[%s] %s\n" ("Error" |> red |> clear) str;
  exit 1

let warn str =
  eprintf "[%s] %s\n" ("Warn" |> yellow |> clear) str

let log at_verbosity str =
  if at_verbosity <= !opt_verbosity then (
    eprintf "[%fs] %s\n" (Sys.time () -. !log_start_time) (Lazy.force str);
    flush stderr
  ) else ()
