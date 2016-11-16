#!/bin/bash

# Chain of goto-cc, goto-instrument, and cbmc

set -e

goto_cc=../../../src/goto-cc/goto-cc
goto_instrument=../../../src/goto-instrument/goto-instrument
cbmc=../../../src/cbmc/cbmc

function usage() {
  echo "Usage: chain.sh <flags> <file>.c"
  exit 1
}

name=$(echo $2 | cut -d. -f1)
flag=$1

$goto_cc -o $name.o $name.c
#$goto_instrument --show-goto-functions $name.o
#$cbmc --show-goto-functions $name.o
$goto_instrument $flag $name.o $name-new.o
$goto_instrument --show-goto-functions $name-new.o
$cbmc $name-new.o

