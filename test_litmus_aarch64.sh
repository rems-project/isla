#!/bin/bash

main() {
    for (( i=0; i<$1; i++ ))
    do
        target/release/isla-axiomatic \
            --config configs/aarch64.toml \
            --arch aarch64.ir \
            --model web/client/dist/aarch64.cat \
            --threads $(( 2 * $1 )) --thread-groups $1 --only-group $i \
            --timeout 10 \
            --test "$2" \
            --cache /tmp/aarch64 \
            --refs "$3" &
        pids[${i}]=$!
    done

    for pid in ${pids[*]}; do
        wait $pid
    done
}

main "$@"
