#!/bin/bash
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
rm results.txt
for f in `find mytests -name "*.alethe" | xargs`
  do
    cargo run check --expand-let-bindings -i $f
    echo $f: $? >> results.txt
  done
