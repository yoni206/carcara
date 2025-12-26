#!/bin/bash
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
CVC5_BIN=`realpath $1`
CARCARA_BIN=`realpath $2`
BENCHMARK=`realpath $3`
PROOF=`realpath /tmp/tmp.alethe`

$CVC5_BIN $BENCHMARK --solve-bv-as-int=sum --dump-proofs --proof-format=alethe --dag-thresh=0 | tail -n+3 | head -n-1 > $PROOF
$CARCARA_BIN check --expand-let-bindings -i $PROOF $BENCHMARK
exit $?
