#!/bin/bash

bench_dir=$1
sat_files=$2
unsat_files=$3
prog=../../../src/main.py

START=$(date +%s)
c=0
s=0
w=0

if [ $sat_files != "-" ]; then
  for i in `cat $sat_files`; do
      printf "$i "
      let "s+=1"
      f="../../$bench_dir/sat/$i"
      "$prog" "$f" > results 2>&1
      cat results
      if [ $? -eq 0 ]; then
        if (grep -q "[^n]sat" results) || (grep -q "^sat" results); then
          echo "Pass!" 
          let "c+=1"
        else
          echo "Wrong!"
          let "w+=1"
          cat "$f" | z3 -dimacs -in
          exit
        fi
      else
        echo "Error"
        cat results
        cat "$f" | z3 -dimacs -in
        exit
      fi
      
      rm -f results
  done
fi

if [ $unsat_files != "-" ]; then
  for i in `cat $unsat_files`; do
      printf "$i "
      f="../../$bench_dir/unsatsat/$i"
      "$prog" "$f" > results 2>&1
        let "s+=1"
      if [ $? -eq 0 ]; then
        if grep -q "unsat" results; then
          echo "Pass!"
          let "c+=1"
        else
          echo "Wrong!"
          let "w+=1"
          cat "$f" | z3 -dimacs -in
          exit
          fi
      else
        echo "Error"
        cat results
        cat "$f" | z3 -dimacs -in
        exit
      fi
      
      rm -f results
  done
fi

echo "-------- Your Result --------"
echo "Pass: $c/$s"

END=$(date +%s)
DIFF=$((  $END - $START ))
echo "Took $DIFF seconds."
