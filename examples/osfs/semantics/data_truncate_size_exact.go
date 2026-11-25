//go:build linux

package semantics

import (
	"os"
)

// An ftruncate's size is exact at a crash (model decision, 2026-11-25;
// pending the user's review).
//
// Decision: a crash leaves a file at its size as of its last sync or at a
// size a change since gave it, where an ftruncate (and open's O_TRUNC) gives
// exactly its target and a pwrite or a fallocate any size from the old size
// to its new one (they move the on-disk size in steps); with a change in
// flight, an ftruncate's target, or for a pwrite or fallocate any size in the
// range data_sizes_since_sync.go allows. The range rule
// (data_sizes_since_sync.go) still bounds the size; this one removes the sizes
// strictly between an ftruncate's old size and its target.
//
// Lean: Impl.lean: OsFile.szCrash (ofDisk, land, synced), OsChangeKind.isTrunc,
// CrashFile (the third size clause); Tests.lean: crash_trunc_size_exact.
//
// Allowed: after the crash below, size 16384 (the synced size) or 20007 or
// 32768 (the targets of the two truncates).
// Excluded: any other size, e.g. 24576 (between 20007 and 32768) or 16385.
//
// Why: documented in the source and measured on configuration C. ext4_setattr
// (fs/ext4/inode.c, Linux 7.0) sets i_disksize to the new size, marks the
// inode dirty and stops the handle in one journal handle, for a growth and a
// shrink alike (a shrink's block freeing after it is completed from the orphan
// list at recovery, at the new size); journal recovery replays a handle whole
// or not at all. Only delayed allocation's writeback (mpage_map_and_submit_extent,
// for pwrite) and ext4_alloc_file_blocks (fallocate, a handle per chunk,
// data_resize_chunks.go) move i_disksize through intermediate sizes.
// Measured: notes/axiom-review/fs-config/trunc-size.sh (a file synced at
// 16384, then a loop of ftruncates to non-page-aligned targets, the device
// frozen at random moments as a power loss and each copy recovered by a
// mount: 40 crashes on 2026-11-25, every recovered size the synced size or one
// of the targets, all 8 of them seen).
//
// Client: bbolt (C-I1, Proof/go_etcd_io/etcd/server/v3/storage/backend/
// CrashInterim.lean): DB.grow truncates the file to a page-aligned size and
// fsyncs before any page is written past the old end, so a crash in that
// window leaves whole pages (bbolt's fileHoldsM).
func TruncateSizeExact(dir string) {
	f, _ := os.Create(dir + "/f")
	f.Truncate(16384)
	f.Sync()          // size 16384
	f.Truncate(20007) // not synced
	f.Truncate(32768)
	// crash here
	// allowed:  16384, 20007, 32768
	// excluded: 16385, 24576, any other size
}
