#!/bin/bash
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
CVC5_BIN=`realpath $1`
CARCARA_BIN=`realpath $2`
BENCHMARK=`realpath /tmp/tmp.smt2`
PROOF=`realpath /tmp/tmp.smt2.alethe`

tee "$BENCHMARK" | $CVC5_BIN -i --solve-bv-as-int=sum --dump-proofs --proof-format=alethe >  $PROOF.tmp
cat $PROOF.tmp | tail -n+3 | head -n-1 > $PROOF
# tee "$BENCHMARK" | $CVC5_BIN -i --solve-bv-as-int=sum --dump-proofs --proof-format=alethe | tail -n+3 | head -n-1 > $PROOF
$CARCARA_BIN check --expand-let-bindings -i $PROOF
exit $?
