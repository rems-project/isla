#!/bin/bash

for i in {0..5}
do
    target/release/isla-axiomatic --arch aarch64.ir \
                                  --model web/client/dist/esop2020.cat \
                                  --threads 12 --thread-groups 6 --only-group $i \
                                  --timeout 10 \
                                  --test ../litmus-tests-armv8a-private/tests/non-mixed-size/@all \
                                  --refs ../litmus-tests-regression-machinery/model-refs/rmem/flat/AArch64.model_logs \
                                  --ifetch &
    pids[${i}]=$!
done

for pid in ${pids[*]}; do
    wait $pid
done
