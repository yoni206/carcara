#!/bin/bash
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
rm $SCRIPT_DIR/mytests/*
grep -lrI solve-bv-as-int ~/git/cvc5/test/regress/cli | xargs grep -l unsat | sort | uniq > list.txt

for f in `cat list.txt`
  do 
    echo "$f"
    base=$(basename "$f")          
    timeout 10 ~/git/cvc5/build/bin/cvc5 $f --solve-bv-as-int=sum --dump-proofs --proof-format=alethe --dag-thresh=0 | tail -n+3 | head -n-1 > $SCRIPT_DIR/mytests/$base.alethe
    cat $f |grep -v '^;' > $SCRIPT_DIR/mytests/$base
  done
