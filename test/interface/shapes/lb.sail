
val thread0 : unit -> unit

function thread0() = {
    thread_init();
    X0 = read_mem((), 64, X1, 8);
    end_instr();
    X2 = to_bits(64, 1);
    end_instr();
    let _ = write_mem((), 64, X3, 8, X2);
}

val thread1 : unit -> unit

function thread1() = {
    thread_init();
    X0 = read_mem((), 64, X1, 8);
    end_instr();
    X2 = to_bits(64, 1);
    end_instr();
    let _ = write_mem((), 64, X3, 8, X2);
}
