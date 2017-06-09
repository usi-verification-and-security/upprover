#!/bin/bash

awk '/VERIFICATION|SUCCESSFUL|FAILED|Aborted|UNKNOWN|identical/{
 print
}
{ a[++d]=$0}

{ a[++d]=$0}'
