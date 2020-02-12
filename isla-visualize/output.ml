open Printf

let opt_verbosity = ref 0

let log_start_time : float ref = ref (Sys.time ())

let fatal str =
  eprintf "[Error] %s\n" str;
  exit 1

let warn str =
  eprintf "[Warn] %s\n" str

let log at_verbosity str =
  if at_verbosity <= !opt_verbosity then (
    eprintf "[%fs] %s\n" (Sys.time () -. !log_start_time) (Lazy.force str);
    flush stderr
  ) else ()
