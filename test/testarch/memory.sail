$ifndef ISLA_MEMORY
$define ISLA_MEMORY

val read_mem = monadic "platform_read_mem" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

val read_mem_ifetch = monadic "platform_read_mem_ifetch" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

val read_mem_exclusive = monadic "platform_read_mem_exclusive" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

val write_mem = monadic "platform_write_mem" : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

val write_mem_exclusive = monadic "platform_write_mem_exclusive" : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

$endif
