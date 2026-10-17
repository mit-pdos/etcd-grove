package raft

import (
	"runtime"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func heapMB() float64 {
	runtime.GC()
	runtime.GC()
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return float64(m.HeapAlloc) / (1 << 20)
}

// The sequence of etcd-io/raft#71: entries of growing size are appended and
// persisted (stableTo) two at a time, so the visible unstable log stays within
// ~64 MB while the backing array keeps every entry ever appended alive.
func TestUnstableRetainedMemoryIssue71(t *testing.T) {
	const mb = 1 << 20
	base := heapMB()
	u := unstable{offset: 1, offsetInProgress: 1, logger: raftLogger}
	next := uint64(1)
	mk := func(size int) pb.Entry {
		e := pb.Entry{Index: next, Term: 1, Data: make([]byte, size)}
		next++
		return e
	}
	ents := make([]pb.Entry, 0, 32)
	for i := 0; i < 17; i++ {
		ents = append(ents, mk(2*mb))
	}
	u.entries = ents
	stable := u.offset
	u.stableTo(stable, 1)
	stable++
	maxVisible := 0
	visible := func() int {
		n := 0
		for _, e := range u.entries {
			n += len(e.Data)
		}
		return n
	}
	for _, r := range []struct{ size, rounds int }{{4, 8}, {8, 4}, {16, 2}, {32, 1}} {
		for i := 0; i < r.rounds; i++ {
			u.truncateAndAppend([]pb.Entry{mk(r.size * mb)})
			if v := visible(); v > maxVisible {
				maxVisible = v
			}
			u.stableTo(stable, 1)
			u.stableTo(stable+1, 1)
			stable += 2
		}
	}
	retained := heapMB() - base
	t.Logf("len=%d cap=%d visible=%d MB (max %d MB) heap retained=%.0f MB",
		len(u.entries), cap(u.entries), visible()/mb, maxVisible/mb, retained)
	runtime.KeepAlive(&u)
	if retained > 2*float64(maxVisible)/mb+8 {
		t.Errorf("unstable retains %.0f MB, more than twice the most it ever held visibly (%d MB)",
			retained, maxVisible/mb)
	}
}

// An array with spare capacity: 60 entries of 1 MB in an array of 100, the
// first 29 persisted. Before #96 the 31 left are copied out (2*31 < cap 71)
// and the persisted 29 MB freed; with #96, 29 > 100/2 and 29 MB > 60 MB / 2
// are both false, so the array, and the persisted entries in it, stay.
func TestUnstableRetainedMemorySpareCap(t *testing.T) {
	const mb = 1 << 20
	base := heapMB()
	u := unstable{offset: 1, offsetInProgress: 1, logger: raftLogger}
	ents := make([]pb.Entry, 0, 100)
	for i := 0; i < 60; i++ {
		ents = append(ents, pb.Entry{Index: uint64(i + 1), Term: 1, Data: make([]byte, mb)})
	}
	u.entries = ents
	ents = nil
	u.stableTo(29, 1)
	retained := heapMB() - base
	t.Logf("len=%d cap=%d heap retained=%.0f MB", len(u.entries), cap(u.entries), retained)
	runtime.KeepAlive(&u)
	if retained > 40 {
		t.Errorf("unstable retains %.0f MB for 31 MB of unstable entries", retained)
	}
}

// The cost of stableTo on a long unstable log, one entry at a time.
func BenchmarkUnstableStableToLongLog(b *testing.B) {
	const n = 10000
	u := unstable{offset: 1, offsetInProgress: 1, logger: raftLogger}
	for i := 0; i < n; i++ {
		u.entries = append(u.entries, pb.Entry{Index: uint64(i + 1), Term: 1, Data: make([]byte, 100)})
	}
	next := uint64(n + 1)
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		u.truncateAndAppend([]pb.Entry{{Index: next, Term: 1, Data: make([]byte, 100)}})
		next++
		u.stableTo(u.offset, 1)
	}
}
