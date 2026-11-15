#!/bin/bash
# run.sh WORKDIR: build main.go with Go 1.27.3 and run it under hard RLIMIT_NOFILE 4..8.
set -u
D=$(cd "$(dirname "$0")" && pwd); W=$1; mkdir -p "$W"
cd "$D" && GOTOOLCHAIN=go1.27.3 GOFLAGS=-mod=mod GO111MODULE=off go build -o "$W/np" main.go || exit 1
for n in 4 5 6 7 8; do
  rm -f "$W/f$n"
  out=$( (ulimit -n $n; "$W/np" "$W/f$n") 2>&1 | head -2 | tr '\n' ' ')
  echo "nofile=$n exists=$([ -e "$W/f$n" ] && echo yes || echo no) :: $out"
done
