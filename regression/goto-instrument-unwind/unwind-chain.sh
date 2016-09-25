#!/bin/bash

src=../../../src
goto_cc=$src/goto-cc/goto-cc
goto_instrument=$src/goto-instrument/goto-instrument
cbmc=$src/cbmc/cbmc

function usage() {
  echo "Usage: chain <options> <testfile>"
  exit 1
}

if [ $# -ne 2 ]; then
  usage
  exit 1
fi

name=$(echo $2 | cut -d. -f1)

$goto_cc -o $name.gb $name.c
$goto_instrument $1 $name.gb ${name}-unwound.gb
$goto_instrument --show-goto-functions ${name}-unwound.gb
$cbmc ${name}-unwound.gb
