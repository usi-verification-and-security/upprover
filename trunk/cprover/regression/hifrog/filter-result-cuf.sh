#!/bin/bash

awk '/ASSERTION(S)|identical|VERIFICATION|Aborted|UNKNOWN/{
 print
}
{ a[++d]=$0}

{ a[++d]=$0}'

