
val thread0 : unit -> unit

function thread0() = {
    thread_init();
    X0 = to_bits(64, 1);
    end_instr();
    let _ = write_mem((), 64, X1, 8, X0);
    end_instr();
    read_mem((), 64, X1, 8)
}
