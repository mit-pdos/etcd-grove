//go:build linux

package semantics

import (
	"os"
)

// A pwrite whose source buffer crosses a page can reach disk torn mid-sector
// (measured; mechanism A).
//
// Decision: none of its own: the byte-level crash rule (data_crash_candidates.go)
// allows a write's prefix new and the rest old, at any byte. The model has no
// "a write stops at a page boundary" rule (the NoTear premise this replaced).
//
// Lean: Impl.lean: CrashFile (each byte any candidate), OsFile.announceWrite;
// Tests.lean: crash_mix (k bytes landed, any k, and any mix).
//
// Allowed: after the crash below, page 0 holds bytes [0,752) new (2) and
// [752,4096) old (1): sector 1 holds both values.
// Excluded: nothing more specific; any byte-wise mix of 1 and 2 is allowed.
//
// Why: measured on C (notes/axiom-review/fs-v2-r6/e2e/: 49 torn images in 5
// runs; and fs-v2-r6/tear/). The copy into the page cache
// (generic_perform_write) runs with page faults disabled; when the second
// source page is being migrated (memory compaction), the copy stops where the
// source crosses a page, 752 bytes in for a buffer at addr%4096 = 0xd10; the
// prefix is committed, the folio unlocked, and writeback can take it before the
// rest is copied. A Go buffer is at any address: stack buffers (minibolt's) and
// etcd's PageWriter flushes (a page-aligned buffer written at a mid-page file
// offset) both cross pages mid-page.
func TornSourcePage(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(4096, 1), 0)
	f.Sync()
	big := make([]byte, 8192)
	buf := big[0xd10 : 0xd10+4096] // crosses a page 752 bytes in, if big is page-aligned
	copy(buf, fill(4096, 2))
	f.WriteAt(buf, 0)
	// crash here (compaction migrating big's second page during the copy,
	// another process's writeback taking the page in the window)
	// allowed: [2 x 752 | 1 x 3344], and any other byte-wise mix
}
