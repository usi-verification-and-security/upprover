#!/bin/bash

awk '/SUMMARIES|SUITABLE|VERIFICATION|identical/{
 print
}
{ a[++d]=$0}

{ a[++d]=$0}'
