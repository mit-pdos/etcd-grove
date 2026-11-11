//go:build linux

package semantics

import (
	"os"
)

// Durable zeros: wherever a file's size is durable, the pages wholly past it
// are zeros on disk, and a crash leaves each byte one of its candidates
// (model decision).
//
// Decision: at a successful sync, a boot and a crash, every byte of a page
// with no byte below the durable size is zero, its one candidate zero (such a
// page has no block, or an unwritten one, which reads as zeros). Nothing else
// orders sizes against data: a crash picks a size in the range since the
// last sync and, independently, one candidate of each byte; a page the
// crash's size does not reach is zeros.
//
// Lean: Impl.lean: diskByte, OsFile.ofDisk, OsFile.synced, CrashFile; the
// header's "Durable zeros"; Tests.lean: crash_new_block_zeros,
// crash_past_end_zeros, crash_current.
//
// Allowed: after the crash below, size 0; or size 4096 with each byte either
// the page's or zero (any byte-wise mix: all of the page, all zeros — the new
// size with the block not yet written —, or a torn mix).
// Excluded: size 4096 with a byte that is neither the page's nor zero (stale
// bytes of a freed block).
//
// Why: measured on configuration C (Linux 7.0, ext4 defaults, dioread_nolock)
// with notes/axiom-review/fs-config/crash.sh (the journal's writes on disk,
// the data's held by dm-delay): empty-write recovers size 1 reading 00,
// append-new size 4097 reading 00 at 4096 (the extent "Uninit"), keep-size
// the same into a FALLOC_FL_KEEP_SIZE extent. ext4 allocates the new block as
// an unwritten extent in the transaction that commits the size, and converts
// it only when the data write completes; an unwritten extent reads zeros, so
// stale bytes never appear (data=ordered's guarantee). With dioread_lock (not
// C) the same run kept size 4096: the commit waited for the data.
// shrink-grow: a file truncated to 100, synced, grown to 8192: the crash
// recovered size 8192 with zeros from 100 on.
//
// Client: bbolt's init writes the four first pages of an empty file and
// fdatasyncs; a crash in between may leave them zeros, both metas invalid,
// and minibolt's Open initializes again (it never trusts a zero meta).
func DurableZeros(dir string) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o600)
	// the directory entry is durable; the file is empty and synced
	page := make([]byte, 4096)
	copy(page, "MAGIC")
	f.WriteAt(page, 0)
	// crash here, before any f.Sync()
	// allowed:  size 0; size 4096, each byte the page's or zero
	// excluded: size 4096 with a byte that is neither
}
