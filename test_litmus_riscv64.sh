#!/bin/bash

main() {
    for (( i=0; i<$1; i++ ))
    do
        target/release/isla-axiomatic \
            --arch riscv64.ir \
            --config configs/riscv64.toml \
            --model web/client/dist/riscv.cat \
            --threads $(( 2 * $1 )) --thread-groups $1 --only-group $i \
            --timeout 10 \
            --test "$2" \
            --cache /tmp/riscv64 \
            --refs "$3" &
        pids[${i}]=$!
    done

    for pid in ${pids[*]}; do
        wait $pid
    done
}

main "$@"
