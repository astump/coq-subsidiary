#!/bin/bash

rm -f wordsby-tests/*.v
rm -f wordsbywf-tests/*.v

for n in 0250 0500 0750 1000 1250 1500 1750 2000 2250 2500 2750 3000; do
  sed "s/NUM/$n/;s/WORDSBY/wordsByl/" TestHarness.v > wordsby-tests/Test$n.v
  sed "s/NUM/$n/;s/WORDSBY/wordsByWf/" TestHarness.v > wordsbywf-tests/Test$n.v
done