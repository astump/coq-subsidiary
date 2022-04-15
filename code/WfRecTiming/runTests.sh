#!/bin/bash

for d in app appendWf1 appendWf ; do 
  echo "========================================="

  for f in $d-tests/Test*.v ; do
    echo "-------------------"
    echo $f
    time coqc -q -R . WfRecTiming $f
  done

done