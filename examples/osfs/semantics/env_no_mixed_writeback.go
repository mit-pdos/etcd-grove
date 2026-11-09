//go:build linux

package semantics

import (
	"os"
)

// No mixed writeback (environment assumption).
//
// Decision: the data one writeback sends never mixes a page's contents before
// and after a concurrent write into it. A sector's crash version is one of
// the versions the page cache had, never a byte-wise mix of two.
//
// Lean: Impl.lean header ("No mixed writeback"); Sector.vers (whole versions
// only); notes/fs-semantics-v2.md, "Environment assumptions".
//
// Allowed: sector 0 is all A or all B after the crash below.
// Excluded: a mix of A and B, from writeback reading the page while the second
// WriteAt copies into it.
//
// Why: assumed. ext4 and xfs do not promise it: without stable pages
// (BDI_CAP_STABLE_WRITES), a write may change a page during its DMA. The
// alternative (model the mix) needs no assumption, but under it etcd's WAL
// cannot be proved to restart: `isTornEntry` needs an all-zero sector, and
// a mix of zeros and data is neither.
func NoMixedWriteback(dir string) {
	f, _ := os.Create(dir + "/f")
	f.WriteAt(fill(512, 'A'), 0)
	go f.Sync()                  // writeback of sector 0 may be under way...
	f.WriteAt(fill(512, 'B'), 0) // ...while this copies into the page
	// crash here
	// allowed:  sector 0 = AAAA..., or BBBB...
	// excluded: sector 0 = AABBA... (a writeback that read the page mid-copy)
}
