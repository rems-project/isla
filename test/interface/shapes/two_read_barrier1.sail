
val thread0 : unit -> unit

function thread0() = {
    thread_init();

    run_instr(0xABCD_0001);
    run_instr(0xABCD_0002);
    run_instr(0xABCD_0003);
}

function clause decode 0xABCD_0001 = {
    X0 = throw_abort(sail_mem_read(plain_read_request(X2, 8)));
}

function clause decode 0xABCD_0002 = {
    sail_barrier(Some(Barrier1));
}

function clause decode 0xABCD_0003 = {
    X1 = throw_abort(sail_mem_read(plain_read_request(X3, 8)));
}
