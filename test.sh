#!/bin/sh

ARGS="-deterministic"

if [ -f main.byte ]; then
    EXEC=./main.byte
elif [ -f main.native ]; then
    EXEC=./main.native
else
    echo "No main.byte nor main.native"
    exit
fi

LOGFILE=test.log
echo -n > "$LOGFILE"

TESTDIR=tests/simple
RAN=0
FAILED=0

function run_test {
    TEST="$1"
    echo -n "Running $TEST ... "
    RES=$($EXEC "$TEST" | grep "^Final" | sed -En 's/.*Val\((.*)\).*/\1/p')
    EXPECTED=$(sed -En 's|// Expected: (.*)$|\1|p' "$TEST")
    if [ "$RES" != "$EXPECTED" ]; then
        echo "failure!"
        echo "Test $TEST failed: Got $RES instead of $EXPECTED" >> $LOGFILE
        FAILED=$(($FAILED+1))
    else
        echo "success."
    fi
    RAN=$(($RAN+1))
}

for TEST in $(ls $TESTDIR/*.s5); do
    run_test "$TEST"
done

echo -n "Ran $RAN tests, $FAILED of them failed"
if [ "$FAILED" -gt 1 ]; then
    echo -n " (see $LOGFILE for the reasons of failure)"
fi
echo "."
