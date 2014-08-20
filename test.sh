#!/bin/sh
function run_test {
    TEST="$1"
    echo "Running $TEST"
    RES=$(./main.byte "$TEST" | sed -En 's/Evaluation done: Val\((.*)\)/\1/p')
    EXPECTED=$(sed -En 's|// Expected: (.*)$|\1|p' "$TEST")
    if [ "$RES" != "$EXPECTED" ]; then
        echo "Test failed: $TEST. Got $RES instead of $EXPECTED"
    fi
}

for TEST in $(ls tests/*.s5); do
    run_test $TEST
done
