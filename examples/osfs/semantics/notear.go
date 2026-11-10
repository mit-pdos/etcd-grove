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
// Why, on configuration C (documented from Linux 7.0's mm/filemap.c, see
// NoTear.lean): generic_perform_write copies a folio at a time under its
// lock; writeback locks the folio; a fatal signal is checked between folios;
// ENOSPC/EDQUOT come from write_begin before a folio's copy; RLIMIT_FSIZE is
// unlimited and ext4's maximum file size with 4 KiB blocks is page-aligned
// (outside C, 1-2 KiB blocks or `ulimit -f 6` cut a one-page write mid-page:
// measured, notes/axiom-review/fs-v2-r4.md N2); write(2) returns an errno only
// when nothing was written. The copy does not fault the source in first: a
// source page that is not mapped (never written by the program, or being
// migrated by compaction) stops the copy there and commits a prefix ending
// where the source crosses a page, which writeback can write (measured on C:
// N1 with userfaultfd; fs-v2-r5.md A1, 1000/1000 writes from fresh heap). So
// the premise rests on a program assumption: each pwrite's buffer address is
// congruent to its file offset mod 4096 (minibolt: 4096- and 16384-byte
// buffers, which go1.27.3's size classes align to 4096 and 8192, at page
// offsets); and on a machine one: no source page is unmapped while the copy
// is inside it (not seen in 3e6 aligned writes under forced compaction;
// assumed). The buffer below is aligned; buf[100:] would not be.
//
// Client: bbolt's meta slot is the 64 bytes at offset 16 of page 0 or 1 (one
// sector), validated by magic, version and an FNV-64a checksum of its first
// 56 bytes. Without NoTear a prefix ending inside the slot gives a torn slot,
// and the crash property needed premise P1 ("no checksum collision on a torn
// meta", examples/osfs/bboltfs/README.md); under NoTear a slot is some whole
// write's or the durable one.
func NoTear(dir string) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR, 0)
	meta := fill(4096, 'M') // one page, every byte written, at a page-aligned offset
	if _, err := f.WriteAt(meta, 0); err != nil {
		// NoTear: nothing of meta landed
		return
	}
	// crash here, before fdatasync
	// allowed under NoTear:  page 0 old or new, whole
	// excluded under NoTear: the first 40 bytes new, the rest old
	// (Impl.lean alone allows it: a short write, or a crash mid-copy)
}
