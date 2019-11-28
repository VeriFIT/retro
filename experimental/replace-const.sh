#!/bin/bash

for file in *.smt2
do
  sed -i '' 's/16000/16/g' ${file}
  sed -i '' 's/32000/32/g' ${file}
done
