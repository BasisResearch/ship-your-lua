#!/bin/bash
# Gate subset (seconds): the quick scripts on Linux must all be accepted.
set -eu
cd "$(dirname "$0")/../.."
tcb/validation/run.sh --quick > /dev/null
O=tcb/validation/out-quick
cat $O/linux.summary
grep -q " rejected 0 " $O/linux.summary
