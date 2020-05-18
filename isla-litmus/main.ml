
open Printf

module GenericHGen = Litmus_test.GenericHGen

let opt_file_arguments = ref ([]:string list)

let opt_stdin = ref false
                       
let options =
  Arg.align [
      ( "--verbosity",
        Arg.Set_int Output.opt_verbosity,
        "<level> Set the logging verbosity to <level>. 0 is silent");
      ( "-v",
        Arg.Unit (fun () -> Output.opt_verbosity := 1),
        " shorthand for --verbosity 1");
      ( "-vv",
        Arg.Unit (fun () -> Output.opt_verbosity := 2),
        " shorthand for --verbosity 2");
      ( "--no-colors",
        Arg.Clear Output.opt_colors,
        " do not use colors in output");
      ( "--stdin",
        Arg.Set opt_stdin,
        " read litmus file from stdin");
    ]

let read_litmus_file (litmus_file_name : string) =
  let ic = open_in litmus_file_name in
  let litmus_test = Litmus_test.read_channel "test" ic (fun _ -> None) in
  let () = close_in ic in
  litmus_test

external memfd_create : string -> Unix.file_descr = "linux_memfd_create"

let read_stdin () =
  let buf = Buffer.create 1024 in
  let rec loop () =
    match input_line stdin with
    | line ->
       Buffer.add_string buf line;
       Buffer.add_char buf '\n';
       loop ()
    | exception End_of_file -> Buffer.to_bytes buf
  in
  loop ()
                                       
let read_litmus_stdin () =
  let contents = read_stdin () in
  let fd = memfd_create "litmus" in
  let wrote = Unix.write fd contents 0 (Bytes.length contents) in
  assert (wrote = Bytes.length contents);
  Unix.fsync fd;
  ignore (Unix.lseek fd 0 Unix.SEEK_SET);
  Litmus_test.read_channel "litmus" (Unix.in_channel_of_descr fd) (fun _ -> None)

let main () =
  let litmus_tests =
    List.map (fun file ->
        match Filename.extension file with
        | ".litmus" ->
           read_litmus_file file
        | _ ->
           Output.fatal (sprintf "Unrecognised file type: %s\n" (Filename.basename file))
      ) !opt_file_arguments
  in

  if !opt_stdin then (
    let litmus_test = read_litmus_stdin () in
    Litmus_test.process litmus_test
  ) else (
    if litmus_tests = [] then
      Output.warn "No .litmus test files";
 
    List.iter Litmus_test.process litmus_tests
  )

let usage_msg = "usage: isla-litmus <files>\n"

let _ =
  Arg.parse options
    (fun s -> opt_file_arguments := !opt_file_arguments @ [s])
    usage_msg;
  main ()
