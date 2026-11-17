//go:build linux

package semantics

import (
	"os"
	"syscall"
)

// The state records which changes were resizes (model bookkeeping; no
// behaviour changes). Pending the user's review (2026-11-14,
// notes/wal-fsext-plan.md §2.5, W1).
//
// Decision: each file keeps the stamps of the resizes (ftruncate, fallocate's
// growth, open's O_TRUNC) announced on it since it was last read from disk (a
// boot or a crash; a new file has none), appended when the resize is
// announced. A sync keeps them (a resize in flight keeps its candidates across
// a sync; stamps are never reused). No step reads the list: every step's
// result, every crash's outcome and every stuck case are what they were
// without it.
//
// Lean: Impl.lean: OsFile.rzs, OsChangeKind.isResize, OsFile.announce (the
// append), OsFile.ofDisk (none). The client premise that reads it: W1
// (LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/W1.lean, AsOfW), which
// asks that an accepted WAL frame read as of one change have every byte's
// candidate stamped by a pwrite, not by a resize.
//
// Allowed: everything the model allowed before (below: at the crash, any size
// and bytes the crash rule gives from the candidates, as without the record).
// Excluded: nothing more.
//
// Why: by construction (the field is read by no step, crash rule or stuck
// condition of Impl.lean, Tree.lean or Paths.lean; the trusted models of os,
// syscall and unix never mention it). It exists because a crash candidate
// keeps a value and a stamp but not the kind of change that announced it: a
// resize announces zeros (OsChange.ofResize), and a pwrite whose data is zeros
// over some bytes announces the same candidates, so a premise that must treat
// the two differently (a frame partly zeroed by wal.cut's truncate is torn; a
// frame whose zero bytes were written by a pwrite is intact) needs the kind.
func ResizeStamps(dir string) {
	f, _ := os.OpenFile(dir+"/f", os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644) // O_TRUNC: a resize, stamp recorded
	f.WriteAt(fill(4096, 0x42), 0)                                         // a pwrite: not recorded
	f.WriteAt(make([]byte, 4096), 4096)                                    // a pwrite of zeros: not recorded
	f.Truncate(100)                                                        // a resize: stamp recorded
	// crash here
	// allowed (as without the record): any size in [0, 8192] the crash rule
	// gives, each byte any of its candidates
	syscall.Fdatasync(int(f.Fd()))
}
