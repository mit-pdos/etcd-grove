//go:build linux

package semantics

import (
	"os"
)

// Ordered growth's assumptions: blocks of at most 4096 bytes, and no block
// past a file's last page after a crash or at boot (environment assumptions).
//
// Decision: freshness is tracked per 4096-byte page (`pageIn`), and every page
// wholly past the size is fresh after a boot, a crash or a successful sync,
// unless the file is `kept` (data_keep_size.go). Both are claims that a page
// the model calls fresh really has no block; if one is false, an append into a
// block that exists is not ordered, and the model wrongly excludes its stale
// outcome (unsound, not merely imprecise).
//
// Lean: Impl.lean: pageIn (4096), OsFile.ofDisk and OsFile.synced
// (`!kept && !pageIn sz n`), OsFile.syncFailed (keeps fresh); the header's
// "Ordered growth".
//
//  1. Block size at most 4096. With 64 KiB blocks, block 0 below holds bytes
//     [0, 65536), so the page at 4096 already has a block, yet pageIn calls it
//     fresh: the append at 5000 is not ordered, and size 5001 with zeros at
//     5000 is reachable on Linux but excluded by the model. Violated by xfs
//     with -b size=64k, 64K-page kernels with 64K blocks, possibly ext4
//     bigalloc (clusters larger than a block; not checked). The x86 mkfs
//     default (4096) is what was tested. Assumed.
//  2. No block past a file's last page after a crash or at boot (except
//     KEEP_SIZE's). A shrinking truncate frees the blocks past the end, and
//     ext4's orphan cleanup and xfs's log recovery finish one a crash
//     interrupted. Assumed; the candidate counterexample is xfs's speculative
//     end-of-file preallocation, which can leave real extents past the end
//     (untested; xfs commits a write's size at I/O completion, so its data is
//     still first).
//  3. A failed sync leaves sectors fresh: an instance of no failed writeback
//     (env_no_failed_writeback.go). Under a real I/O error ext4 could commit
//     the size and the new block with the data unwritten.
func BlockSize(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(100, 'a'), 0)
	f.Sync() // size 100; one block (4 KiB: bytes [0, 4096))
	f.WriteAt([]byte{'b'}, 5000)
	// crash here
	// with 4 KiB blocks (assumed): any size in [100, 5001]; at 5001, byte
	// 5000 is 'b'
	// with 64 KiB blocks (excluded by the assumption): also size 5001 with
	// 00 at 5000
}
