#!/bin/bash
cat $1 | ./solve_and_check.sh ~/git/cvc5/build/bin/cvc5 target/debug/carcara
