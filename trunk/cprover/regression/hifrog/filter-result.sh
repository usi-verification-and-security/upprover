#!/bin/bash

awk '/SUMMARIES|SUITABLE|VERIFICATION|SUCCESSFUL|identical/{
 print
}
{ a[++d]=$0}

{ a[++d]=$0}'
