#!/bin/bash

cd ..
for d in List/wordsby-tests List/wordsbywf-tests ; do 
  echo "========================================="

  for f in $d/Test*.v ; do
    echo "-------------------"
    echo $f
    time coqc -q -impredicative-set -R . Subsidiary $f
  done

done

cd List