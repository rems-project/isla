#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o pipefail

bsd_license() {
    cat <<EOF
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
EOF
}

funding() {
    cat <<EOF 
This software was developed by the University of Cambridge Computer
Laboratory (Department of Computer Science and Technology), in part
under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), in part funded by
EPSRC Programme Grant EP/K008528/1 "REMS: Rigorous Engineering for
Mainstream Systems", and in part funded from the European Research
Council (ERC) under the European Union’s Horizon 2020 research and
innovation programme (grant agreement No 789108, "ELVER").
EOF
}

strip_header() {
    awk '(NR == 1 && /^[/][/]/), /^$/' "$1" | wc -l
}

author_info() {
    printf "$1 BSD 2-Clause License\n$1\n"
    local authors=$(git log --invert-grep --grep LICENSE_UPDATE --follow --pretty=format:'%aN' "$2" \
                        | sort | uniq -c | sort -t ' ' -k 1 -n -r | sed 's/^\s*[0-9]\+\s*//' | sed '/\[bot\]$/d')
    while IFS= read -r author; do
        local years=$(git log --follow --author="$author" --pretty=format:'%ad' --date=format:'%Y' "$2" \
                          | sort -n | uniq | perl -pe 'chomp if eof' | tr '\n' ',' | sed 's/,/, /g')
        printf "$1 Copyright (c) $years $author\n"
    done <<< "$authors"
    printf "$1\n"
    bsd_license | awk "{ if (length(\$0) == 0) print \"$1\"; else print \"$1 \" \$0; }"
}

author_info_global() {
    printf "BSD 2-Clause License\n\n"
    local authors=$(git log --invert-grep --grep LICENSE_UPDATE --pretty=format:'%aN' \
                        | sort | uniq -c | sort -t ' ' -k 1 -n -r | sed 's/^\s*[0-9]\+\s*//' | sed '/\[bot\]$/d')
    while IFS= read -r author; do
        local years=$(git log --author="$author" --pretty=format:'%ad' --date=format:'%Y' \
                          | sort -n | uniq | perl -pe 'chomp if eof' | tr '\n' ',' | sed 's/,/, /g')
        printf "Copyright (c) $years $author\n"
    done <<< "$authors"
    printf "\n"
    bsd_license
    printf "\n"
    funding
}

main() {
    while IFS= read -r file; do
        local old_header_len=$(strip_header "$file")
        local new_body=$(tail -n +"$old_header_len" "$file")
        local new_header=$(author_info '//' "$file")
        echo -n "$new_header" > "$file.nh"
        printf "\n" >> "$file.nh"
        echo -n "$new_body" >> "$file.nh"
        printf '\n' >> "$file.nh"
        mv "$file.nh" "$file"
    done <<< $(git ls-files '*.rs' '*.lalrpop')

    author_info_global '' '' > LICENSE
}

main

