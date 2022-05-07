#!/bin/bash

cd ..
for d in wordsByl wordsByWf wordsByP ; do  # 
  echo "========================================="

  for f in List/$d-tests/Test*.v ; do
    echo "-------------------"
    echo $f
    time coqc -q -impredicative-set -R . Subsidiary $f
    time coqc -q -impredicative-set -R . Subsidiary $f
    time coqc -q -impredicative-set -R . Subsidiary $f
  done

done

cd List