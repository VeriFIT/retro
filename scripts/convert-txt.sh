#!/bin/bash

for file in ../equations/*.txt
do
  b=$(basename ${file})
  python3 smt_convert.py ${file} > ../equations/kaluza-hard/${b}.smt2
done
