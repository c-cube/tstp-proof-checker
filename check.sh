#!/bin/sh

# simple script to check derivations
echo "check $1"

exec ./src/main.native $@
