
let opt_model = ref None
let opt_events = ref []
              
let options =
  Arg.align [
      ( "--input",
        Arg.String (fun str -> opt_model := Some str),
        "SMT model produced by (get-model) with z3");
    ]

let usage_msg = "usage: isla-visualize <options>\n"
  
let main () =
  Arg.parse options (fun ev -> opt_events := !opt_events @ [ev])
    usage_msg;
  match !opt_model with
  | None ->
     prerr_endline "No input file";
     exit 1
  | Some input_file ->
     let in_chan = open_in input_file in
     let contents = really_input_string in_chan (in_channel_length in_chan) in
     let sexprs = Sat_model.sexpr_of_sat_model contents in
     Sat_model.interpret_sat_output [0; 1] !opt_events sexprs; 
     exit 0

let _ = main ()
