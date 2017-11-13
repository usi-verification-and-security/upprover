#!/bin/bash

awk '/ASSERTION(S)|SUBSTITUTED|SUITABLE|identical|VERIFICATION|Aborted|UNKNOWN/{
 print
}
{ a[++d]=$0}

/Violated property/{
 for(i=d;i<=d;i++){ print a[i] }
 for(o=1;o<=3;o++){ getline;  print}
 delete a
 d=0
}
{ a[++d]=$0}'
