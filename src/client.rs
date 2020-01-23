// MIT License
//
// Copyright (c) 2019 Alasdair Armstrong
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use crossbeam::queue::SegQueue;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::io::prelude::*;
use std::os::unix::net::UnixStream;
use std::process::exit;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use isla_lib::concrete::Sbits;
use isla_lib::executor;
use isla_lib::executor::Frame;
use isla_lib::init::initialize_letbindings;
use isla_lib::ir::*;
use isla_lib::litmus::assemble_instruction;
use isla_lib::smt::Checkpoint;

mod opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn read_message<R: Read>(reader: &mut R) -> std::io::Result<String> {
    let mut length_buf: [u8; 4] = [0; 4];
    reader.read_exact(&mut length_buf)?;
    // Use i32 because OCaml doesn't have a u32 type
    let length = i32::from_le_bytes(length_buf);

    let mut buf = vec![0; usize::try_from(length).expect("message length invalid")];
    reader.read_exact(&mut buf)?;
    Ok(String::from_utf8_lossy(&buf).to_string())
}

fn write_message<W: Write>(writer: &mut W, message: &str) -> std::io::Result<()> {
    let length: [u8; 4] = i32::to_le_bytes(i32::try_from(message.len()).expect("message length invalid"));
    writer.write(&length)?;
    writer.write(message.as_bytes())?;
    Ok(())
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.reqopt("", "socket", "connect to server at location", "<path>");

    let (matches, arch) = opts::parse(&opts);
    let CommonOpts { num_threads, mut arch, symtab, initial_registers, isa_config } =
        opts::parse_with_arch(&opts, &matches, &arch);

    insert_primops(&mut arch, AssertionMode::Optimistic);

    let register_state = initial_register_state(&arch, initial_registers);
    let letbindings = Mutex::new(HashMap::new());
    let shared_state = Arc::new(SharedState::new(symtab, &arch));

    initialize_letbindings(&arch, &shared_state, &register_state, &letbindings);

    let socket_path = matches.opt_str("socket").unwrap();
    let mut stream = match UnixStream::connect(&socket_path) {
        Ok(stream) => stream,
        Err(e) => {
            eprintln!("Could not connect to socket {}: {:?}", socket_path, e);
            return 1;
        }
    };

    match read_message(&mut stream) {
        Ok(message) => println!("Got: {}", message),
        Err(_) => (),
    }

    write_message(&mut stream, "Hello, OCaml!");

    0
}
