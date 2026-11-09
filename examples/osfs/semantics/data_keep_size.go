//go:build linux

package semantics

import (
	"os"

	"golang.org/x/sys/unix"
)

// fallocate(FALLOC_FL_KEEP_SIZE) changes nothing (model decision).
//
// Decision: a keep-size fallocate is the FallocKeep step with no effect but
// its errno: the blocks it allocates past the end are unwritten extents,
// which read as zeros until written, exactly as durable zeros say a page past
// the size is (data_durable_zeros.go). No special case follows it.
//
// Lean: Impl.lean: the FallocKeep step (`st' = st`); Falloc.lean:
// wp_osFallocKeep.
//
// Allowed: after the crash below, size 1; size 4097 with the page's data;
// size 4097 with zeros from byte 1 on (the size committed, the unwritten
// extent not yet converted).
//
// Why: measured on configuration C (notes/axiom-review/fs-config/crash.sh
// keep-size: a 4096-byte synced file, fallocate -k 4096 4096 synced, pwrite at
// 4096, journal on disk and data delayed: size 4097 reading 00 at 4096). etcd
// uses KEEP_SIZE only through fileutil.Preallocate(…, extendFile=false); its
// WAL uses extendFile=true (mode 0); walfs's seglog.go calls both.
func KeepSize(dir string) {
	f, _ := os.Create(dir + "/f")
	f.Write([]byte{0x00})
	unix.Fallocate(int(f.Fd()), unix.FALLOC_FL_KEEP_SIZE, 0, 1<<20)
	f.Sync() // size 1, unwritten blocks allocated past the end
	f.WriteAt(fill(4096, 'P'), 1)
	// crash here
	// allowed: size 1; size 4097 with P...; size 4097 with zeros
}
