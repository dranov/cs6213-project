#!/bin/bash

set -x

source ../env.sh

tlc() {
  java -cp $TLA_TOOLS -XX:+UseParallelGC tlc2.TLC -workers auto -userFile user.txt "$@" > tlc.txt
}

tla2json() {
  java -jar $TLA2JSON "$@"
}

clean() {
  rm -rf raftexample-* states *.json *.txt
}

clean
tlc $SPEC
tla2json tlc.txt > full.json
$INTERPRETER/raftexample -nodes 3 -file full.json -debug > output.txt 2>&1
