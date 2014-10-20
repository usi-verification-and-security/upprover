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
#cbmc --show-claims --bounds-check --signed-overflow-check --unsigned-overflow-check cases1.c | grep "Claim" | sed "s/Claim //" | sed "s/://" > tempclaims.log
#cbmc --show-claims dfa.c | grep "Claim" | sed "s/Claim //" | sed "s/://" > tempclaims.log
#cbmc --show-claims $bench.c | grep "Claim" | sed "s/Claim //" | sed "s/://" > tempclaims.log
#i=1
#echo ""
#for line in $(cat tempclaims.log)
#  do
#    #echo $line
#    numid[$line]=$i
#    alfid[$i]=$line
#    i=$(($i + 1))
#  done
##rm tempclaims.log

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

declare -A mayimply

echo "Reading potential implication relationships..."

while read line
do
  #echo $line
  stronger=${numid[$(echo $line | cut -f 1 -d " ")]}
  weaker=${numid[$(echo $line | cut -f 2 -d " ")]}
  #echo "mapping $stronger to $weaker"
  mayimply[$weaker]+=" $stronger"
done < __red_may_impl #  __hl_may_impl

echo "done."
echo ""

#echo ""
#echo "Printing mayimply"
#
#for i in "${!mayimply[@]}"
#do
#  echo "key  : $i"
#  echo "value: ${mayimply[$i]}"
#done

tocheck=""
declare -A checked

#for claim in $(seq 1 $claims)
#do
#  checked[$claim]=0
#done

for i in "${!alfid[@]}"
do
  checked[$i]=0
done

echo "Number of weak claims: $(cat __hl_weaker | wc -l)"

for claim in $(cat __hl_weaker)
do
  #echo "Claim: $claim"
  #echo "numid: ${numid[$claim]}"
  #echo ""
  tocheck+=" ${numid[$claim]}"
done

#echo "Arrivato qui!"
#echo "tocheck vale: $tocheck"

mkdir $bench.res 2>/dev/null
mkdir $bench.res/claims 2>/dev/null
mkdir $bench.res/claims/sum 2>/dev/null

(echo $tocheck | grep -E "[0-9]") 2>/dev/null
status=$?
while [ $status -eq 0 ]
do
  tocheck=$(echo $tocheck | tr " " "\n" | sort -g -u | tr "\n" " ")

  claim=$(echo $tocheck | cut -f 1 -d " ")
  tocheck=$(echo $tocheck | sed -e 's/^\w*\ *//')
  #tocheck=$(echo $tocheck | cut -d' ' -f2-)
      if [ ${checked[$claim]} -eq 0 ]
      then
  checked[$claim]=1
  echo "Checking claim $claim (${alfid[$claim]}) ..."
  echo "Command: evolcheck $options --claim $claim $bench"
  (exec > $bench.res/claims/$claim.log 2>&1; $FUNFROG $options --claim $claim $bench)
  (exec 2> /dev/null; cp "__summaries" $bench.res/claims/sum/$claim.sum)
  cat $bench.res/claims/$claim.log | grep "VERIFICATION SUCCESSFUL"
  ecode=$?
  if [ $ecode -eq 0 ]
  then
    echo "Verification ok. need to check what's going on with the stronger claims"
    strongers=${mayimply[$claim]}
    echo "Checking the $(echo $strongers | wc -w) stronger claims..."

    for w in $strongers
    do
      if [ ${checked[$w]} -eq 0 ]
      then
        echo "Adding claim $w"
        tocheck+=" $w"

else
echo "Already Checked: $w"
      fi
    done
    echo "Done."
  else
    strongers=${mayimply[$claim]}
    echo "It is already failed! No need to check $(echo $strongers | wc -w) stronger claims..."
  fi
  echo ""
  fi
  echo $tocheck | grep -E "[0-9]"
  status=$?
done
