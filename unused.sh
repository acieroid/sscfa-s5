#!/bin/sh
if [ $# -ne 1 ]; then
    echo "Expected file as argument"
    exit
fi

sed -nE "s/.*(^| )let \(%([a-zA-Z0-9]+) = .*/\2/p" "$1" > /tmp/ids.log > /tmp/ids.log
for id in $(cat /tmp/ids.log); do
    COUNT=$(grep "$id" "$1" | wc -l)
    if [ $COUNT -eq 1 ]; then
        echo $id
    fi
done
