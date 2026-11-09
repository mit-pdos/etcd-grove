//go:build linux

package semantics

import (
	"os"

	"golang.org/x/sys/unix"
)

// fallocate(FALLOC_FL_KEEP_SIZE) makes no page known to have no block (model
// decision).
//
// Decision: a keep-size fallocate changes nothing a read sees, but marks the
// file `kept` for good (through syncs and crashes): no sector is fresh from
// then on, so ordered growth no longer applies to that file.
//
// Lean: Impl.lean: OsFile.kept, OsFile.keepAlloc, the FallocKeep step,
// OsFile.ofDisk and OsFile.synced (fresh only if `!kept`).
//
// Allowed: after the crash below, size 1; size 4097 with the page's data;
// size 4097 with block 1's old contents (zeros: unwritten extents read as
// zeros, but the model does not rely on it).
// Excluded: none of these.
//
// Why: assumed from how ext4 and xfs work: the blocks past the end exist
// before the append, so the append allocates nothing and is not ordered (the
// same case as data_append_old_block.go, measured there for the block holding
// the end). Not separately tested. etcd uses KEEP_SIZE only through
// fileutil.Preallocate(…, extendFile=false); its WAL uses extendFile=true
// (mode 0).
func KeepSize(dir string) {
	f, _ := os.Create(dir + "/f")
	f.Write([]byte{0x00})
	unix.Fallocate(int(f.Fd()), unix.FALLOC_FL_KEEP_SIZE, 0, 1<<20)
	f.Sync() // size 1, blocks allocated past the end
	f.WriteAt(fill(4096, 'P'), 1)
	// crash here
	// allowed: size 1; size 4097 with P...; size 4097 with old block bytes
}
