//go:build linux

package semantics

import (
	"os"
)

// NoTear: a pwrite that lands only partly stops at a page boundary; a failed
// one lands nothing (trace-level assumption of the theorems that use it, not
// part of the semantics).
//
// Decision: theorems over `fsSemWithS NoTearStep NoTearCrash` hold of the runs
// where every write that lands partly (at its return, or at a crash) lands a
// *page cut*: none, all, or a prefix ending on a 4096-byte boundary; and a
// pwrite that returns an errno wrote nothing. A write within one page lands
// whole or not at all.
//
// Lean: NoTear.lean: PageCut, NoTearStep, NoTearCut, NoTearCrash, inPage,
// pageCut_inPage, noTearStep_keeps; FilteredSem.lean, AdequacyS.lean
// (fsSQ_crash_adequacy).
//
// Allowed under NoTear: after the crash below, page 0 holds the old meta or
// the new one, whole.
// Excluded under NoTear: a prefix of the write ending inside the page (e.g.
// 40 bytes landed, a slot half old, half new); a failed write that changed
// the file.
//
// Why: argued from the kernel source, to be reviewed: generic_perform_write
// copies a page at a time under the page's lock; writeback locks the page; a
// fatal signal is checked between pages; ENOSPC/EDQUOT come from write_begin
// before a page's copy; EFAULT (which can cut mid-page) cannot happen on Go
// memory. The semantics (Impl.lean) lets a short or failed pwrite land any
// byte prefix, so a sector's versions can include one that is half old, half
// new; sector atomicity then keeps that torn version whole. bbolt needs
// NoTear: its meta slot is the 64 bytes at offset 16 of page 0 or 1 (one
// sector), validated by magic, version and an FNV-64a checksum of its first
// 56 bytes. Without NoTear a prefix ending inside the slot gives a torn slot,
// and the crash property needed premise P1 ("no checksum collision on a torn
// meta", examples/osfs/bboltfs/README.md); under NoTear a slot is some whole
// write's or the durable one. Assumed, to be reviewed against the kernel.
func NoTear(dir string) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR, 0)
	meta := fill(4096, 'M') // one page, at a page-aligned offset
	if _, err := f.WriteAt(meta, 0); err != nil {
		// NoTear: nothing of meta landed
		return
	}
	// crash here, before fdatasync
	// allowed under NoTear:  page 0 old or new, whole
	// excluded under NoTear: the first 40 bytes new, the rest old
	// (Impl.lean alone allows it: a short write, or a crash mid-copy)
}
