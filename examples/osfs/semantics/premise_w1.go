//go:build linux

package semantics

import (
	"os"
)

// W1: a client premise, assumed for etcd's crash theorems (etcd_safe's members;
// the WAL tester's crash theorem, tQ). Pending the owner's review (etcd-dist D6
// Q2, 2026-11-24).
//
// Decision: a premise on crashes, not a rule of the semantics. The etcd
// examples' file semantics etcdFsSem restricts crashes by etcdCQ = W1 walCodec:
// at a crash, every frame (its 8-byte length word and its record, not its
// padding) that a fresh WAL reader accepts in a .wal file of the crashed tree
// came back as of one change: as of the file's last sync, or as of some change n
// by which each of its bytes was last written by a pwrite (not by a resize's
// zeros). The general crash rule allows any byte-wise mix of each byte's
// candidates (data_crash_candidates.go); W1 removes the mixes that the reader
// accepts, which on etcd's codec means a torn frame whose torn data matches its
// torn CRC-32C field (a collision), a frame torn only in its record's Type field,
// or the intended frame with part of it zeros not yet announced by a pwrite.
//
// Lean: Proof/go_etcd_io/etcd/server/v3/storage/wal/W1.lean: W1, AsOfOne, AsOfW,
// W1Sat (a crash keeping every byte as of the last sync satisfies it, so it
// never leaves a state without a crash), AsOfW.not_rz_window, AsOfW.split_zero;
// examples/lib/etcdstart/FsExts.lean: etcdCQ, etcdFsSem.
//
// Allowed under the premise: after the crash below, the tail frame comes back
// whole as written (as of the pwrite), or as the preallocated zeros (as of the
// sync; the reader stops at a zero length), or any torn mix that the reader
// rejects (its CRC-32C does not match: decoder.go's ErrCRCMismatch, a torn tail).
// Excluded under the premise: a torn mix that the reader accepts.
// Without the premise (the semantics): any mix.
//
// Why: etcd relies on the CRC to reject a torn tail (decoder.go:133-150, the WAL
// W3 decision "no CRC32-C collision on torn data", notes/decisions.md); the W4c
// crash-point runs of the WAL tester never saw an accepted torn frame. What W1
// excludes beyond collisions (a torn Type field, unannounced zeros) is listed in
// W1.lean's docstring for the review. Assumed (the CRC's), measured as support.
func W1Premise(dir string) {
	f, _ := os.Create(dir + "/0000000000000000-0000000000000000.wal")
	f.Truncate(64 * 1024 * 1024) // preallocated: zeros
	f.Sync()
	frame := fill(4096+16, 'F') // a frame (length word, record) spanning a page boundary
	f.WriteAt(frame, 0)
	// crash here
	// allowed (premise): the frame whole, zeros, or a torn mix the reader rejects
	// excluded (premise): a torn mix the reader accepts (a CRC-32C collision)
}
