#!/bin/bash

for d in app appendWf1 appendWf ; do 
  mkdir -p $d-tests
  rm -f $d-tests/*.v

  for n in 0200 0400 0600 0800 1000 1200 1400 1600 1800 2000 2200 2400; do
    sed "s/NUM/$n/;s/APP/$d/" TestHarness.v > $d-tests/Test$n.v
  done
done