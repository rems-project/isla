#!/bin/sh

require_tool () {
    echo "Checking have $1"
    if which $1
    then
        echo "yes"
    else
        echo "no"
        exit 1
    fi
}

build_z3 () {
    # Check if our environment has at least the most basic tools
    require_tool git
    require_tool python
    require_tool g++

    # Checkout z3 if we haven't already
    if [ ! -d "z3" ]; then
        git clone https://github.com/Z3Prover/z3.git
    fi
    cd z3
    git checkout tags/z3-4.8.7
    python scripts/mk_make.py --staticlib
    cd build
    make -j 12
}

vendor () {
    mkdir -p vendor
    cd vendor
    build_z3
    exit 0
}

vendor || exit 1
