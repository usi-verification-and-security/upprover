#!/bin/bash

# $1 benchmark name
# $2 graph/nograph
# $3 funfrog options
# $4 divisor
# $5 tred
# $6 forward/backward traversal

export FUNFROG=../evolcheck
export SCRIPTS="$PWD"

bench=$1
usegraph=$2
options=$3
divisor=$4
strategy=$5
usetred=$6

mildiv () 
{ 
    int=$(($1 * 1000 / $2 / 1000));
    frac=$(($1 * 1000 / $2 % 1000));
    prefix="";
    if [ "$(($frac < 100))" == "0" ]; then
        prefix="";
    else
        prefix="0";
        if [ "$(($frac < 10))" == "0" ]; then
            prefix="0";
        else
            prefix="00";
        fi;
    fi;
    echo $int.$prefix$frac
}

exec_time () 
{ 
    ts=$(date +%s%N);
    eval $1;
    tt=$((($(date +%s%N) - $ts)/1000000));
    echo "$(mildiv $tt 1000)"
}

implred () 
{ 
    ( IFS=$'\n';
    ( printf "digraph {\n";
    ( cat __hl_may_impl | awk -F" " '{print $3,$4}' | sed 's/ / -> /' | sed 's/$/;/' );
    printf "}\n" ) | tred | tr -d ' ' | tr -d '\t' | tr -d ';' | sed '1d;$d' | sed 's/->/ /' > __redresult.log;
    for line in $(cat __redresult.log);
    do
        grep $line __hl_may_impl;
    done > __red_may_impl )
}

if [[ $usegraph != "graph" ]]
then
  if [[ $usegraph != "nograph" ]]
  then
    exit 1
  fi
fi

#if [ -f $bench ]; then mv -b $bench $bench.bak; fi
#cp $bench $bench.out

rm --force __*

#in the latest version, this is automatic
#{ $FUNFROG/funfrog-dai $options --show-claims $bench ; } >mapping.log 2>&1

if [[ $usegraph == "graph" ]]
then
  echo -n "Detecting implications..."
  echo -n "Temporary file" > __just_hl_dep
  echo "Done. Time: $(exec_time "{ $FUNFROG --no-itp $options --claims-order $divisor $bench ; } >__impl_det.log 2>&1")"
  if [[ $usetred == "tred" ]]
  then
    echo -n "Executing transitive reduction..."
    echo "Done. Time: $(exec_time "implred")"
  else
    cp __hl_may_impl __red_may_impl
  fi
  rm __just_hl_dep
else
  echo -n "Detecting reachable assertions..."
  echo -n "Temporary file" > __just_hl_dep
  echo "Done. Time: $(exec_time "{ $FUNFROG --no-itp $options --claims-order 100000000 $bench ; } >__reachable.log 2>&1")"  
  rm __just_hl_dep
fi

if [[ $strategy == "forward" ]]
then
  suffix="_strong"
else
  suffix="_weak"
fi

if [[ $usegraph == "nograph" ]]
then
  echo -n "Checking all reachable assertions one by one..."
  suffix="all"
  tred=""
else
  echo -n "Traversing implication graph and checking assertions one by one..."
fi

if [[ $usetred == "tred" ]]; then usetred="_$usetred"; fi

echo "Done. Time: $(exec_time "$SCRIPTS/hlcheck$suffix.sh $bench \"--no-itp $options\" >\"__one_by_one_${usegraph}${usetred}.log\" 2>&1")"

#rm $bench
#if [ -f $bench.bak ]; then mv $bench.bak $bench; fi

