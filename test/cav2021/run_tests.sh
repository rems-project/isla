#!/bin/bash

run_tests() {
    local threads="$1"
    local thread_multiplier="$2"
    local sample="$3"
    local test="$4"
    local refs="$5"
    local id="$6"
    local cat="$7"
    shift 7
    local extra_args=("$@")
    
    printf "===== Test set %s =====\n" "$id"
    for (( i=0; i<threads; i++ ))
    do
        target/release/isla-axiomatic \
            --config configs/aarch64.toml \
            --arch "$ISLA_SNAPSHOT_DIR/aarch64.ir" \
            --model "web/client/dist/$cat.cat" \
            --threads $(( thread_multiplier * threads * sample )) --thread-groups $(( threads * sample )) --only-group "$i" \
            --test "$test" \
            --cache /tmp/aarch64 \
            --refs "$refs" \
            "${extra_args[@]}" &
        pids[${i}]=$!
    done

    result="ok"
    for pid in ${pids[*]}; do
        if ! wait $pid; then
            result="fail"
        fi
    done

    rm /tmp/aarch64/isla_candidate_*
    results["$id"]="$result"
}

main() {
    DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )/../.." && pwd )"
    cd "$DIR" || exit 1

    threads=$(dc -e "[4]sM $(nproc) d 4 >M 2 / p")
    printf "Using %s threads\n" "$threads"
    printf "ARM test directory: %s\nSnapshot directory: %s\n" "$ARM_TEST_DIR" "$ISLA_SNAPSHOT_DIR"

    local args=()
    
    args=("--check-sat-using" "(par-or smt (then dt2bv simplify solve-eqs qe bv))")
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/BASIC_2_THREAD/@all" "test/cav2021/results.model_logs" "AArch64 2 thread" "aarch64" "${args[@]}"
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/BASIC_3_THREAD/@all" "test/cav2021/results.model_logs" "AArch64 3 thread" "aarch64" "${args[@]}"
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/EXCLUSIVES/@all" "test/cav2021/results.model_logs" "AArch64 exclusives" "aarch64" "${args[@]}"
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/DMB_LD/@all" "test/cav2021/results.model_logs" "AArch64 DMB_LD" "aarch64" "${args[@]}"
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/PPO/@all" "test/cav2021/results.model_logs" "AArch64 PPO" "aarch64" "${args[@]}"

    args=("--ifetch" "--check-sat-using" "(par-or smt (then dt2bv simplify solve-eqs qe bv))")
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/BASIC_2_THREAD/@all" "test/cav2021/results.model_logs" "AArch64 2 thread (ifetch)" "esop2020" "${args[@]}"
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/BASIC_3_THREAD/@all" "test/cav2021/results.model_logs" "AArch64 3 thread (ifetch)" "esop2020" "${args[@]}"
    run_tests "1" "$threads" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/EXCLUSIVES/@all" "test/cav2021/results.model_logs" "Exclusives (ifetch)" "esop2020" "${args[@]}"
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/DMB_LD/@all" "test/cav2021/results.model_logs" "AArch64 DMB_LD (ifetch)" "esop2020" "${args[@]}"
    run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/PPO/@all" "test/cav2021/results.model_logs" "AArch64 PPO (ifetch)" "esop2020" "${args[@]}"
 
    printf "\n===== AARCH64 SUMMARY =====\n"
    for i in "${!results[@]}"
    do
        printf "Test set %s %s\n" "$i" "${results[$i]}"
    done

    for i in "${!results[@]}"
    do
        if [ "${results[$i]}" = "fail" ]; then
            exit 1
        fi
    done
}

declare -A results
main "$@"
