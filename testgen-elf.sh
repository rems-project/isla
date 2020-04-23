#!/bin/sh

set -ex

aarch64-linux-gnu-as -o test.o test.s
aarch64-linux-gnu-ld -m aarch64elf -static -o test.elf -T test.ld -n test.o
