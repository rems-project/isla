#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o pipefail

dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

declare -a tests

gather_at_file() {
    local atdir="$(dirname -- $1)"
    while IFS= read -r line
    do
        if [[ ${line::1} == "@" ]]; then
            gather_at_file "${atdir%%/}/$line" "$2"
        else
            if test -f "${atdir%%/}/$line"; then
                tests=("${tests[@]}" "$(basename -- ${line%.*}).toml")
                isla-litmus ${atdir%%/}/$line > ${2%%/}/$(basename -- ${line%.*}).toml
            fi
        fi
    done < "$1"
}

print_json() {
    printf '[\n  {\n    "section": "%s",\n    "model": "%s",\n    "tests": [\n' "$1" "$2"
    for (( i=0; i<"${#tests[@]}-1"; i++ ))
    do
        printf '      "%s",\n' "${tests[i]}"
    done
    printf '      "%s"\n    ]\n' "${tests[${#tests[@]}-1]}"
    printf '  }\n]\n'
}

main() {
    gather_at_file "$@"
    print_json "$3" "$4"
}

main "$@"
