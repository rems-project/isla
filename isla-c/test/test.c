#include <stdio.h>

#include "../src/isla.h"

void test(void) {
     isla_source *source;
     isla_symtab *symtab;
     isla_ir *ir;
     isla_shared_state *shared_state;

     source = isla_source_load("test/test.isla_ir");
     symtab = isla_symtab_new();
     ir = isla_symtab_intern(symtab, source, true);
     shared_state = isla_shared_state_new(symtab, ir);

     isla_shared_state_free(shared_state);
     isla_symtab_free(symtab);
     isla_ir_free(ir);
     isla_source_free(source);
}

int main(void) {
     test();
     return 0;
}
