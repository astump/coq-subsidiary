#!/bin/bash

for d in wordsByl wordsByWf wordsByP ; do  
  mkdir -p $d-tests
  rm -f $d-tests/*.*
  rm -f $d-tests/.??*

  for n in 0250 0500 0750 1000 1250 1500 1750 2000 2250 2500 2750 3000; do
#  for n in 1000 2000 3000 4000 5000 6000 7000 8000 9000; do      
#  for n in 020 040 060 080 100 120 140 160 180 200 220 240 260 280 300; do
    sed "s/NUM/$n/;s/WORDSBY/$d/" TestHarness.v > $d-tests/Test$n.v
  done

done