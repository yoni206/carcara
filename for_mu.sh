#!/bin/bash
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
CVC5_BIN=/home/ubuntu/git/cvc5/build/bin/cvc5
CARCARA_BIN=/home/ubuntu/git/carcara/target/debug/carcara
BENCHMARK=`realpath /tmp/tmp.smt2`
PROOF=`realpath /tmp/tmp.smt2.alethe`

trap 'kill $(jobs -p)' SIGABRT
$CVC5_BIN -i --solve-bv-as-int=sum --dump-proofs --proof-format=alethe --err=$PROOF.tmp
# tee "$BENCHMARK" | $CVC5_BIN -i --solve-bv-as-int=sum --dump-proofs --proof-format=alethe --err=$PROOF.tmp
# cat $PROOF.tmp | tail -n+3 | head -n-1 > $PROOF
# $CARCARA_BIN check --expand-let-bindings -i $PROOF
exit $?
