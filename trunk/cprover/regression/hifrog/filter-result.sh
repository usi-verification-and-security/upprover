#!/bin/bash

awk '/VERIFICATION|SUCCESSFUL|FAILED|identical/{
 print
}
{ a[++d]=$0}

{ a[++d]=$0}'
