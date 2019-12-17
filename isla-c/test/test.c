#include <stdio.h>

#include "../src/isla.h"

ISLA_COLLECTOR(all_unsat) {

}

void test(void) {
     isla_source *source;
     isla_symtab *symtab;
     isla_ir *ir;
     isla_shared_state *shared_state;
     //isla_register_state *register_state;
     isla_task *task;

     source = isla_source_load("test/test.isla_ir");
     symtab = isla_symtab_new();
     ir = isla_symtab_intern(symtab, source, true);
     shared_state = isla_shared_state_new(symtab, ir);
     //register_state = isla_register_state_new(ir);
     //initialize_registers(register_state, ir);

     //task = isla_task("prop", register_state);
     bool b;
     void *collect = &b;
     isla_start_threaded_executor(8, task, shared_state, collect, all_unsat);

     isla_shared_state_free(shared_state);
     isla_symtab_free(symtab);
     isla_ir_free(ir);
     isla_source_free(source);
}

int main(void) {
     test();
     return 0;
}
