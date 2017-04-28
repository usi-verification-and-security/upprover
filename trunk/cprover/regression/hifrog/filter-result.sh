#!/bin/bash

awk '/SUMMARIES|VERIFICATION|SUCCESSFUL|FAILED|identical/{
 print
}
{ a[++d]=$0}

{ a[++d]=$0}'
