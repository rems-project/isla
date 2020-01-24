let opt_arch_path = ref None

let options = Arg.align ([
  ( "--arch",
    Arg.String (fun path -> opt_arch_path := Some path),
    "<path> load architecture file")
])

let read_exact sock_fd exact =
  let rec read_exact_offset buff ofs =
    let nbytes = Unix.read sock_fd buff ofs (exact - ofs) in
    let ofs = ofs + nbytes in
    if ofs = exact then
      ()
    else if ofs > exact then
      failwith "Read too many bytes"
    else
      read_exact_offset buff ofs
  in
  let buff = Bytes.create exact in
  read_exact_offset buff 0;
  buff

let read_message sock_fd =
  let header = read_exact sock_fd 4 in
  let length = Int32.to_int (Bytes.get_int32_le header 0) in
  let body = read_exact sock_fd length in
  Bytes.to_string body

let write_message sock_fd str =
  let body = Bytes.of_string str in
  let length = Int32.of_int (Bytes.length body) in
  let header = Bytes.create 4 in
  Bytes.set_int32_le header 0 length;
  let msg = Bytes.concat Bytes.empty [header; body] in
  let _ = Unix.write sock_fd msg 0 (Int32.to_int length + 4) in
  ()

let connect arch_path =
  let sock_fd = Unix.(socket PF_UNIX SOCK_STREAM 0) in
  let sock_path =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "isla%d.socket" (Random.bits ())) in
  print_endline sock_path;
  Unix.(bind sock_fd (ADDR_UNIX sock_path));
  Unix.listen sock_fd 1;

  let isla_client_path = Filename.concat (Sys.getcwd ()) "isla-client" in
  let pid =
    Unix.(create_process isla_client_path
            [|"isla-client"; "--socket"; sock_path; "--arch"; arch_path|]
            stdin stdout stderr) in

  let sock_fd, _ = Unix.accept sock_fd in
  print_endline "Connected";

  sock_fd

let main () =
  Random.self_init ();
  Arg.parse options (fun _ -> ()) "";

  let arch_path = match !opt_arch_path with
    | Some path -> path
    | None ->
       prerr_endline "No architecture specified via --arch option";
       exit 1
  in

  let sock_fd = connect arch_path in
  write_message sock_fd "execute_asm str w0, [x1]";
  write_message sock_fd "execute_asm sub sp, sp, #16";
  let response = read_message sock_fd in
  print_endline response;

  ()

let _ = main ()
