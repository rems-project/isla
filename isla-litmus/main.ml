
open Printf

module GenericHGen = Litmus_test.GenericHGen

let opt_file_arguments = ref ([]:string list)

let opt_cat_libdir = ref "."

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
    ]

let read_litmus_file (litmus_file_name : string) =
  let ic = open_in litmus_file_name in
  let litmus_test = Litmus_test.read_channel "test" ic (fun _ -> None) in
  let () = close_in ic in
  litmus_test

let main () =
  let litmus_tests =
    List.map (fun file ->
        let contents = match Filename.extension file with
          | ".litmus" ->
             read_litmus_file file
          | _ ->
             Output.fatal (sprintf "Unrecognised file type: %s\n" (Filename.basename file))
        in
        Filename.basename file, contents
      ) !opt_file_arguments
  in

  if litmus_tests = [] then
    Output.warn "No .litmus test files";

  List.iter Litmus_test.process litmus_tests

let usage_msg = "usage: sail-axiomatic <files>\n"

let _ =
  Arg.parse options
    (fun s -> opt_file_arguments := !opt_file_arguments @ [s])
    usage_msg;
  main ()
