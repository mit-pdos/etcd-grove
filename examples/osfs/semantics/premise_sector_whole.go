//go:build linux

package semantics

import (
	"os"
)

// SectorWhole: a client premise, assumed only for etcd's WAL (a known
// limitation).
//
// Decision: not part of the semantics. A theorem about etcd's WAL may assume,
// of its crashes, that every 512-byte sector of the WAL's files comes back as
// one state of that sector: as it was right after some change, each change
// either applied whole or not at all. The general crash rule allows any
// byte-wise mix (data_crash_candidates.go); this premise removes the mixes
// within a sector, for the covered files only.
//
// Lean: Premises.lean: SectorWhole (covers), valAt, fsSemWithS (the premise as
// a crash filter); Tests.lean: sectorWhole_durable (a crash satisfying it
// always exists).
//
// Allowed under the premise: after the crash below, sector 0 holds the record
// whole or the preallocated zeros, and sector 1 likewise, independently.
// Excluded under the premise: a sector holding part of the record and part
// zeros. Without the premise (the semantics): any mix.
//
// Why: etcd's WAL assumes it. Its decoder calls a damaged last record torn
// (repairable) only if some 512-byte chunk of it is all zeros (decoder.go,
// isTornEntry); a sector that is part record, part zeros makes it report
// corruption, and the member does not start. The premise is false of C in
// general (data_torn_source_page.go, data_mixed_writeback.go); the WAL's own
// code reaches one of those mechanisms (PageWriter writes its page-aligned
// buffer at mid-page file offsets) and was not caught failing on disk in 202
// crash images (notes/axiom-review/fs-v2-r6/wal/,
// nonissues/etcd-wal-torn-tail-mid-sector.md). Assumed, as a known limitation
// (notes/STATUS.md), so that the WAL's proof can rely on it.
func SectorWholePremise(dir string) {
	f, _ := os.Create(dir + "/0.wal")
	f.Truncate(64 * 1024 * 1024) // preallocated: zeros
	f.Sync()
	rec := fill(1024, 'R') // a record spanning sectors 0 and 1
	f.WriteAt(rec, 0)
	// crash here
	// allowed (premise): sector 0 in {RRRR, 0000}, sector 1 in {RRRR, 0000}
	// excluded (premise): a sector mixing R and 0
}
