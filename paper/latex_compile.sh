#!/bin/bash

latexmk -pdf -file-line-error -halt-on-error "$1" > latex.log 2>&1

if [ $? -ne 0 ]; then
    grep "^./main.tex:" latex.log
    sed -n -e "/^.\/$1:[1-9]/,/Transcript written/p" latex.log
    sed -n -e "/^Runaway argument/,/Transcript written/p" latex.log
    rm -f *.fdb_latexmk
    exit 1
else
    exit 0
fi
