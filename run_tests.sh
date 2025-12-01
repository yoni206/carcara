#!/bin/bash
SCRIPT_DIR="$(dirname "$(realpath "$0")")"
rm results.txt
for f in `realpath mytests/*.alethe`
  do
    cargo run check -i $f
    echo $f: $? >> results.txt
  done
