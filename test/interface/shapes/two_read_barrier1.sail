
val thread0 : unit -> unit

function thread0() = {
    thread_init();

    start_instr(0xABCD_0001);
    X0 = throw_abort(sail_mem_read(plain_read_request(X2, 8)));
    end_instr();
    
    start_instr(0xABCD_0002);
    sail_barrier(Barrier1);
    end_instr();

    start_instr(0xABCD_0003);
    X1 = throw_abort(sail_mem_read(plain_read_request(X3, 8)));
    end_instr();
}
