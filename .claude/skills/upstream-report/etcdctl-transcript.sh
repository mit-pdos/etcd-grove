#!/usr/bin/env bash
# Usage: etcdctl-transcript.sh <etcd-clone> <base-sha> <commands-file>
#
# Builds etcd and etcdctl at <base-sha> (cached in ~/etcd-fixes/.bin/<sha>/), starts a single-member cluster on a
# fresh data directory and free ports, runs each non-empty line of <commands-file> with bash (`etcdctl` is the
# base build, pointed at the cluster; `;` joins commands on one line), and prints a console transcript: `$ <line>`,
# then its output. The transcript is what goes into the issue, verbatim. Lines starting with `#` are skipped.
# `--bin DIR` uses binaries already built at the base instead.
set -euo pipefail

bin=""
if [[ "${1:-}" == --bin ]]; then bin=$2; shift 2; fi
[[ $# -eq 3 ]] || { sed -n '2,9p' "$0" >&2; exit 2; }
clone=$1 sha=$2 cmds=$3

if [[ -z "$bin" ]]; then
	full=$(git -C "$clone" rev-parse --verify "$sha^{commit}")
	short=$(git -C "$clone" rev-parse --short=9 "$full")
	bin=~/etcd-fixes/.bin/$short
	if [[ ! -x $bin/etcd || ! -x $bin/etcdctl ]]; then
		src=$(mktemp -d)
		git -C "$clone" worktree add -q --detach "$src/etcd" "$full"
		ld="-X go.etcd.io/etcd/api/v3/version.GitSHA=$short"
		mkdir -p "$bin"
		(cd "$src/etcd/server" && go build -ldflags "$ld" -o "$bin/etcd" .) >&2
		(cd "$src/etcd/etcdctl" && go build -ldflags "$ld" -o "$bin/etcdctl" .) >&2
		git -C "$clone" worktree remove --force "$src/etcd"
		rmdir "$src"
	fi
fi

port() { python3 -I -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])'; }
cport=$(port) pport=$(port)
data=$(mktemp -d)
"$bin/etcd" --data-dir "$data" \
	--listen-client-urls "http://127.0.0.1:$cport" --advertise-client-urls "http://127.0.0.1:$cport" \
	--listen-peer-urls "http://127.0.0.1:$pport" --initial-advertise-peer-urls "http://127.0.0.1:$pport" \
	--initial-cluster "default=http://127.0.0.1:$pport" >"$data.log" 2>&1 &
pid=$!
trap 'kill $pid 2>/dev/null || true; wait $pid 2>/dev/null || true; rm -rf "$data" "$data.log"' EXIT
for _ in $(seq 50); do
	"$bin/etcdctl" --endpoints="127.0.0.1:$cport" endpoint health >/dev/null 2>&1 && break
	sleep 0.2
done

echo "\$ etcd --version"
"$bin/etcd" --version
echo "\$ etcdctl version"
"$bin/etcdctl" version
echo "---"
while IFS= read -r line; do
	[[ -z "$line" || "$line" == \#* ]] && continue
	echo "\$ $line"
	ETCDCTL_ENDPOINTS="127.0.0.1:$cport" PATH="$bin:$PATH" bash -c "$line" 2>&1 || true
done <"$cmds"
