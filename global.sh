#!/bin/sh
sed -En 's/.*let \((%[a-zA-Z0-9]+) = .*/\1/p' $1
