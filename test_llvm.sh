#!/bin/bash
if [ $# -ne 2 ]; then
  echo "Invalid number of arguments"
else
  FILES="${2}/*.lat"
  for f in ${FILES}
  do
    echo $f
     ./"${1}" "${f}"
  done
  cd "${2}"
  FILES="*.lat"
  for f in ${FILES}
  do
    if [ -f "${f::-4}".bc ]; then
      echo "${f} compiled"
      FILE="${f::-4}".input 
      if [ -f "$FILE" ]; then
          lli "${f::-4}".bc<"$FILE">tmp.out
      else 
          lli "${f::-4}".bc>tmp.out
      fi

      diff tmp.out "${f::-4}".output
      rm "${f::-4}".ll
      rm "${f::-4}".bc
      rm tmp.out
    else
      echo "${f} not compiled"  
    fi
  done
fi
