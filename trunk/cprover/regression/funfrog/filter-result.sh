#!/bin/bash

awk '/^SAT|^UNSAT|SUMMARIES|ASSERTION|SUITABLE|trivial/{
 print
}
{ a[++d]=$0}

/Violated/{
 for(i=d;i<=d;i++){ print a[i] }
 for(o=1;o<=3;o++){ getline;  print}
 delete a
 d=0
}
{ a[++d]=$0}'
