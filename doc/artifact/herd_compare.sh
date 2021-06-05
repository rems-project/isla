#!/bin/bash

main() {
    tmpfile=$(mktemp /tmp/herdcompare.XXXXX)
    results=$(mktemp /tmp/herdresults.XXXXX)
    herd7 "$1" > "$tmpfile" || true
    mcompare7 -show r -nohash "$tmpfile" "$2" > "$results" || true
    forbidden_ok=$(grep -c -E "Forbid[[:space:]]+Forbid" "$results")
    allowed_ok=$(grep -c -E "Allow[[:space:]]+Allow" "$results")
    forbidden_err=$(grep -c -E "Allow[[:space:]]+Forbid" "$results")
    allowed_err=$(grep -c -E "Forbid[[:space:]]+Allow" "$results")
    printf "Forbidden correct: %s\n" "$forbidden_ok"
    printf "Allowed correct: %s\n" "$allowed_ok"
    printf "Total correct %s\n" "$(dc -e "$allowed_ok $forbidden_ok + p")"
    printf "Forbidden but should be allowed: %s\n" "$forbidden_err"
    printf "Allowed but should be forbidden: %s\n" "$allowed_err"
    rm "$tmpfile" || true
    rm "$results" || true
}

main "$@"
