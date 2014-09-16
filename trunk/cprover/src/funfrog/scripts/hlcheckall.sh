#!/bin/bash
# $1 benchmark name
# $2 evolcheck options

bench=$1
options=$2

echo "Benchmark: $bench"
echo "Options: $options"
echo ""

declare -A numid
declare -A alfid

#echo -n "Using cbmc to map numeric identifiers..."
##cbmc --show-claims dfa.c | grep "Claim" | sed "s/Claim //" | sed "s/://" > tempclaims.log
##cbmc --show-claims $bench.c | grep "Claim" | sed "s/Claim //" | sed "s/://" > tempclaims.log
#cbmc --show-claims --bounds-check --signed-overflow-check --unsigned-overflow-check cases1.c | grep "Claim" | sed "s/Claim //" | sed "s/://" > tempclaims.log
#i=1
#echo ""
#for line in $(cat tempclaims.log)
#  do
#    #echo $line
#    numid[$line]=$i
#    alfid[$i]=$line
#    i=$(($i + 1))
#  done
#rm tempclaims.log

while read line
do 
  claimnum=$(echo $line | cut -f 1 -d " ")
  claimid=$(echo $line | cut -f 2 -d " ")
  numid[$claimid]=$claimnum
  alfid[$claimnum]=$claimid
  #echo "Relating number ${numid[$claimid]} with id ${alfid[$claimnum]}"
done < __mapping

#  echo "Number: $(echo $line | cut -f 1 -d " "), Id: $(echo $line | cut -f 2 -d " ")"; done < __mapping

#claims=$(($i - 1))

#echo "Printing numid"
#
#for i in "${!numid[@]}"
#do
#  echo "key  : $i"
#echo "value: ${numid[$i]}"
#done

#echo ""
#echo "Printing alfid"
#
#for i in "${!alfid[@]}"
#do
#  echo "key  : $i"
#  echo "value: ${alfid[$i]}"
#done

echo "done."
echo ""

#echo "Number of claims: $claims"
#echo ""

mkdir $bench.res 2>/dev/null
mkdir $bench.res/claimsn 2>/dev/null
mkdir $bench.res/claimsn/sum 2>/dev/null

for claim in $(cat __hl_list | sort -u)
do
  echo "${numid[$claim]}" | grep -q '[0-9]'
  notempty=$?
  if [ $notempty = 0 ]
  then
    echo "Checking claim ${numid[$claim]} ($claim) ..."
    echo "Command: FUNFROG/evolcheck $options --claim ${numid[$claim]} $bench.out"
    (exec > $bench.res/claimsn/${numid[$claim]}.log 2>&1; $FUNFROG $options --claim ${numid[$claim]} $bench.out)
    (exec 2> /dev/null; cp "__summaries" $bench.res/claimsn/sum/${numid[$claim]}.sum)
    cat $bench.res/claimsn/${numid[$claim]}.log | grep "VERIFICATION FAILED"
    ecode=$?
    if [ $ecode -eq 0 ]
    then
      echo "Verification failed"
    else
      echo "Verification successful!"
    fi
  fi
  echo ""
done
