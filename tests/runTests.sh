#!/usr/bin/env bash
FAIL=false
for i in tests/*.test ;
do
    if ! ($i > /dev/null 2>&1) then echo $i failed ; FAIL=true;
    fi;
done
if $FAIL ; then exit 2 ; fi
