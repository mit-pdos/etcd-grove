#!/bin/sh
# Runs Main N times (default 100), each in its own process; prints how many panicked.
cd "$(dirname "$0")/../.." || exit 1
n=${1:-100}
GOTOOLCHAIN=go1.27.3 go test -c -o /tmp/tcpwritedeadline.test ./axiomcx/tcp-writedeadline/ || exit 1
p=0
i=0
while [ $i -lt $n ]; do
	if /tmp/tcpwritedeadline.test -test.run '^TestMainPanics$' -test.count=1 >/dev/null 2>&1; then
		p=$((p + 1))
	fi
	i=$((i + 1))
done
echo "$p of $n runs panicked"
