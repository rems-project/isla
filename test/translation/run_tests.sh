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
            --armv8-page-tables \
            --config configs/aarch64_mmu_on.toml \
            --footprint-config configs/aarch64.toml \
            --arch "$ISLA_SNAPSHOT_DIR/aarch64.ir" \
            --model "$CAT_DIR/$cat.cat" \
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
    printf "ARM test directory: %s\nSnapshot directory: %s\nCat directory: %s\n" "$ARM_TEST_DIR" "$ISLA_SNAPSHOT_DIR" "$CAT_DIR"

    local args=()
    
    args=("--check-sat-using" "(then dt2bv solve-eqs qe simplify bv)")
    #run_tests "$threads" "2" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/BASIC_2_THREAD/@all" "test/translation/results.model_logs" "AArch64 2 thread MMU weakest" "aarch64_mmu_weakest" "${args[@]}"
    run_tests "1" "6" "$1" "$ARM_TEST_DIR/tests/non-mixed-size/BASIC_2_THREAD_EXTRA/@all" "test/translation/AArch64.model_logs" "AArch64 2 thread MMU strong" "aarch64_mmu_strong" "${args[@]}"
 
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
