
val thread0 : unit -> unit

function thread0() = {
    thread_init();
    X0 = read_mem((), 64, X2, 8);
    end_instr();
    X1 = read_mem((), 64, X3, 8);
}
