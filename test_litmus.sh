#!/bin/bash

for i in {0..35}
do
    target/release/isla-axiomatic --arch aarch64.ir \
                                  --model web/client/dist/aarch64.cat \
                                  --threads 72 --thread-groups 36 --only-group $i \
                                  --timeout 20 \
                                  --tests ../litmus-tests-armv8a-private/tests/non-mixed-size/@all \
                                  --refs ../litmus-tests-regression-machinery/model-refs/rmem/flat/AArch64.model_logs &
    pids[${i}]=$!
done

for pid in ${pids[*]}; do
    wait $pid
done
