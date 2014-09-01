#!/bin/sh
if [ -f main.native ]; then
    EXEC=main.native
elif [ -f main.byte ]; then
    EXEC=main.byte
else
    echo "No main.native nor main.byte, launch make first"
    exit 1
fi

echo "Loading envs/full-decls.s5"
./main.native -dump full.env envs/full-decls.s5 -no-gc -deterministic >/dev/null
echo "Loading envs/full-mods.s5"
./main.native -dump full.env -env full.env envs/full-mods -restricted-gc -deterministic >/dev/null
