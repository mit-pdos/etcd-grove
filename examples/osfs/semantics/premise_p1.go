//go:build linux

package semantics

import (
	"os"
)

// P1: a client premise, assumed only for minibolt's crash theorem.
//
// Decision: not part of the semantics. minibolt's crash safety (bootCrashSafety)
// assumes, of its crashes, that a meta slot (the 64 bytes at offset 16 of page 0
// or 1) of the crash image that passes minibolt's validate (magic, version, and
// the FNV-64a checksum of its first 56 bytes) is the slot as it was right after
// one change. The general crash rule allows any byte-wise mix of a slot's states
// (data_crash_candidates.go); the premise removes only the mixes that validate.
//
// Lean: Proof/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/BootP1.lean:
// P1, BootCrashSafety; P1Sat.lean: p1_crash_exists (a crash satisfying it always
// exists), p1_untouched (a file no change touched never makes it fail); valAt
// (Premises.lean).
//
// Allowed under the premise: after the crash below, the slot holds the old meta
// (valid), the new meta (valid), or any mix of the two that fails validate.
// Excluded under the premise: a mix of the two that validates. Without the
// premise (the semantics): any mix.
//
// Why: a torn meta must not be taken for a real one; minibolt, like bbolt, relies
// on the checksum to reject it. For minibolt's runs the premise removes no real
// crash: between two syncs a slot holds one of two states (zeros and meta(j) in
// init, meta(t-2) and meta(t) in commit t), and no byte-wise mix of any such
// pair validates except the two states themselves, enumerated for every txid up
// to the 1 GiB bound (notes/axiom-review/fs-final/p1mix/, 2.2 M mixes, 0 found).
// In general it is bbolt's assumption that a torn meta does not collide on its
// checksum. Measured (enumerated) for minibolt; assumed in general.
func P1Premise(dir string, oldMeta, newMeta []byte) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR, 0o600)
	page := make([]byte, 4096)
	copy(page[16:], oldMeta)
	f.WriteAt(page, 0)
	f.Sync() // the slot durable as oldMeta
	copy(page[16:], newMeta)
	f.WriteAt(page, 0) // commit: the new meta into the same slot
	// crash here
	// allowed (premise): slot = oldMeta, slot = newMeta, or a mix failing validate
	// excluded (premise): a mix of oldMeta and newMeta that validates
}
