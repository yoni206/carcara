#!/bin/bash
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
rm $SCRIPT_DIR/mytests/generated/*.smt2
rm $SCRIPT_DIR/mytests/generated/*.alethe
rm $SCRIPT_DIR/mytests/crafted/*.alethe
grep -lrI solve-bv-as-int ~/git/cvc5/test/regress/cli | xargs grep -l unsat | sort | uniq > list.txt
find $SCRIPT_DIR/mytests/crafted -name "*.smt2" >> list.txt

for f in `cat list.txt | grep cvc5.*regress`
  do 
    echo "$f"
    base=$(basename "$f")          
    timeout 5 ~/git/cvc5/build/bin/cvc5 $f --solve-bv-as-int=sum --dump-proofs --proof-format=alethe | tail -n+3 | head -n-1 > $SCRIPT_DIR/mytests/generated/$base.alethe
    cat $f |grep -v '^;' > $SCRIPT_DIR/mytests/generated/$base
  done

for f in `cat list.txt | grep mytests.crafted`
  do 
    echo "$f"
    base=$(basename "$f")          
    timeout 5 ~/git/cvc5/build/bin/cvc5 $f --solve-bv-as-int=sum --dump-proofs --proof-format=alethe | tail -n+3 | head -n-1 > $SCRIPT_DIR/mytests/crafted/$base.alethe
  done
