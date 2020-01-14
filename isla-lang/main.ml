open Isla_lang_ast

module Lexer = Isla_lang_lexer
module Parser = Isla_lang_parser
module PP = Isla_lang_parser_pp



let input_file = ref( None : string option)
               
let opts = [
  ("-i",
    Arg.String (fun s -> input_file := Some s),
    Printf.sprintf "<string> input file");
  ]
         
let usage = "Usage: just main (for interactive) or main -i <filename> (for batch)\n" ^
              "       main -help   to show options"

let usage' = usage ^ "\n" (*^ "Options:"*)
let help outchan msg =
  Printf.fprintf outchan "%s\n\n" msg
let collect_file s = help stderr "illegal argument"; exit 1

let _ = 
  begin try Arg.parse_argv Sys.argv (Arg.align opts) collect_file usage' with
        | Arg.Bad msg  -> help stderr msg; exit 1
        | Arg.Help msg -> help stdout msg; exit 0
  end


let process linebuf =
  try
    (* Run the generated lexer and parser on this input *)
    let t = (Parser.term_start Lexer.token linebuf) in
    (* Show the generated raw and "pretty" pp of the result *)
    Printf.printf "   "; PPrintEngine.ToChannel.compact stdout (PP.pp_raw_term t); Printf.printf "\n";
    Printf.printf "   "; PPrintEngine.ToChannel.compact stdout (PP.pp_term t); Printf.printf "\n"
  with
  | Lexer.Error msg ->
      Printf.fprintf stdout "%s" msg
  | Parser.Error ->
      Printf.fprintf stdout "%s^\nAt offset %d: syntax error.\n" (String.make (Lexing.lexeme_start linebuf) ' ') (Lexing.lexeme_start linebuf)
  

let _ =
  match !input_file with
  | None -> 
     begin
       Printf.printf "enter isla-footprint terms\n";
       let rec foo () =
         let line = read_line () in
         let linebuf = Lexing.from_string line in
         process linebuf; flush stdout in
       foo ()
     end
  | Some f ->
     let c = open_in f in
     let linebuf = Lexing.from_channel c in
     process linebuf
     
