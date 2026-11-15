#!/bin/bash
# fs-v2-r6 (b): build addr (main.go: BootMinibolt as a plain main) with go1.27.3, print the
# compiler's escape decisions for minibolt's write buffers, run it BOOTS times on a filesystem of
# configuration C under strace, and tabulate every pwrite64 by (length, offset % 4096,
# buffer address % 4096).
# Usage: addr.sh WORKDIR [BOOTS]
set -u
H=$(cd "$(dirname "$0")" && pwd)
. "$H/../../fs-config/mkfs-mount.sh"
D=${1:?workdir}; N=${2:-200}
mkdir -p "$D"
sudo umount "$D/mnt" 2>/dev/null
L=$(c_mkfs "$D/c.img")
c_mount "$L" "$D/mnt"
c_check "$D/mnt" || exit 1
(cd "$H" && GOTOOLCHAIN=go1.27.3 GOFLAGS=-mod=mod GOPROXY=off go build -o "$D/addr" .) || exit 1
(cd "$H/../../../../examples" && GOTOOLCHAIN=go1.27.3 go build -gcflags=-m ./osfs/bboltfs/ 2>&1 \
  | grep -E 'minibolt.go:[0-9]+:[0-9]+: make\(\[\]byte')
strace -f -qq -e trace=pwrite64 -e raw=pwrite64 -o "$D/st.out" "$D/addr" "$D/mnt" "$N"
python3 -I - "$D/st.out" <<'EOF'
import re, sys, collections
c = collections.Counter()
for l in open(sys.argv[1]):
    m = re.search(r'pwrite64\((0x[0-9a-f]+), (0x[0-9a-f]+), (0x[0-9a-f]+), (0x[0-9a-f]+|0)\)', l)
    if m:
        fd, a, n, o = [int(x, 16) for x in m.groups()]
        c[(n, o % 4096, a % 4096, hex(a))] += 1
seen = collections.Counter()
for (n, o, a, full), v in sorted(c.items()):
    seen[(n, o, a)] += v
for (n, o, a), v in sorted(seen.items()):
    print(f"pwrite64 len {n:5d}  off%4096 {o}  addr%4096 {a:#05x}  x{v}")
EOF
sudo umount "$D/mnt"; sudo losetup -d "$L"
