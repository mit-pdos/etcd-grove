//go:build linux

package semantics

import (
	"os"
)

// A page rewritten while its previous writeback is in flight can reach disk as
// a byte-wise mix of the two writes (measured; mechanism B).
//
// Decision: none of its own: the byte-level crash rule
// (data_crash_candidates.go) allows any mix of a byte's candidates. The model
// has no "no mixed writeback" assumption (which this replaced: measured false
// on C).
//
// Lean: Impl.lean: CrashFile; Tests.lean: crash_mix.
//
// Allowed: after the crash below, the page holds any byte-wise mix of 1 and 2,
// at arbitrary bytes, sector 0 included.
// Excluded: a byte that is neither 1 nor 2.
//
// Why: measured on C (notes/axiom-review/fs-v2-r6/e2e/, run B1: aligned
// buffer, no compaction, 16,707 torn images in 749,451 writebacks, 15,833 of
// them with a mixed sector). ext4 unlocks a folio once its writeback has
// started, before the device has read it; on a device without stable pages
// (C's virtio disk, its loop and dm devices: stable_writes = 0) the next pwrite
// changes the folio during the transfer (LWN "Stable pages", 2011: "Current
// kernels will, in most situations, allow a process to modify a page while the
// writeback operation is in progress."). A successful fsync between the writes
// prevents it: it waits for the writeback.
func MixedWriteback(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(4096, 1), 0)
	f.Sync()
	f.WriteAt(fill(4096, 2), 0) // writeback of this version starts (another process's sync)
	f.WriteAt(fill(4096, 3), 0) // the page changes while the device reads it
	// crash here
	// allowed: any byte-wise mix of 1, 2 and 3
}
