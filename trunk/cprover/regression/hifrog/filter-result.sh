#!/bin/bash

awk '/VERIFICATION|SUCCESSFUL|FAILED|Aborted|identical/{
 print
}
{ a[++d]=$0}

{ a[++d]=$0}'
