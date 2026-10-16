---
upstream: unchecked
checked:
links:
---

# raft: `MemoryStorage.CreateSnapshot` panics outside `[firstIndex-1, lastIndex]`, undocumented

**Status**: open (not reported upstream).

**Where** (etcd-io/raft at `40f8be730b18`, the revision `etc/goose.py` pins):

- `storage.go:226-229`: `CreateSnapshot`'s documentation: "CreateSnapshot makes a snapshot
  which can be retrieved with Snapshot() and can be used to reconstruct the state at that
  point. If any configuration changes have been made since the last compaction, the result
  of the last ApplyConfChange must be passed in." Nothing about the range of `i`.
- `storage.go:233-245`: after the `ErrSnapOutOfDate` check (`i <= ms.snapshot.Metadata.Index`),
  `if i > ms.lastIndex() { getLogger().Panicf(...) }`, then
  `ms.snapshot.Metadata.Term = ms.ents[i-offset].Term` with `offset := ms.ents[0].Index`.

**What happens**: two panics on an `i` newer than the snapshot:

- `i > lastIndex()`: `Panicf("snapshot %d is out of bound lastindex(%d)")`;
- `i < offset` (an index the storage has compacted away, possible because `Compact` does not
  move the snapshot: `Compact(4)` on a fresh storage leaves `snapshot.Metadata.Index = 0`
  and `offset = 4`): `i-offset` wraps around and `ms.ents[i-offset]` is a runtime
  "index out of range" panic -- where `Compact`, `Term` and `Entries` return `ErrCompacted`
  for the same kind of index.

Reproduction (in package `raft`, `go test -run TestMemoryStorageCreateSnapshot -v`):

```go
func TestMemoryStorageCreateSnapshotBelowCompaction(t *testing.T) {
	ms := NewMemoryStorage()
	_ = ms.Append([]pb.Entry{{Index: 1, Term: 1}, {Index: 2, Term: 1},
		{Index: 3, Term: 1}, {Index: 4, Term: 1}, {Index: 5, Term: 1}})
	_ = ms.Compact(4)
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("no panic")
		} else {
			t.Logf("panic: %v", r) // index out of range [18446744073709551614] with length 2
		}
	}()
	_, _ = ms.CreateSnapshot(2, nil, nil)
}

func TestMemoryStorageCreateSnapshotPastLastIndex(t *testing.T) {
	ms := NewMemoryStorage()
	_ = ms.Append([]pb.Entry{{Index: 1, Term: 1}})
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("no panic")
		} else {
			t.Logf("panic: %v", r) // snapshot 2 is out of bound lastindex(1)
		}
	}()
	_, _ = ms.CreateSnapshot(2, nil, nil)
}
```

**How it happens**: past the `ErrSnapOutOfDate` check, `CreateSnapshot` reads the term at
`ms.ents[i-offset]`, where `offset` is the index of the storage's first (dummy) entry. Only the
upper bound is checked, by a `Panicf`. Nothing checks `i >= offset`, and the range below it is
reachable because `Compact` moves `offset` but not the snapshot. The first test above runs:

1. A fresh storage holds only the dummy entry at index 0 (`snapshot.Metadata.Index = 0`).
2. `Append` entries 1 to 5: `ms.ents` is indices 0 to 5.
3. `Compact(4)`: `ms.ents` is indices 4 (the new dummy) and 5, so `offset = 4`;
   the snapshot index stays 0.
4. `CreateSnapshot(2, nil, nil)`: `2 > 0` passes the out-of-date check and `2 <= 5` the
   bound check; `i - offset = 2 - 4` wraps to `18446744073709551614`, and `ms.ents[...]`
   panics with "index out of range [18446744073709551614] with length 2".

```go
// storage.go:230-243 (etcd-io/raft 40f8be7)
func (ms *MemoryStorage) CreateSnapshot(i uint64, cs *pb.ConfState, data []byte) (pb.Snapshot, error) {
	ms.Lock()
	defer ms.Unlock()
	if i <= ms.snapshot.Metadata.Index {
		return pb.Snapshot{}, ErrSnapOutOfDate
	}

	offset := ms.ents[0].Index
	if i > ms.lastIndex() {
		getLogger().Panicf("snapshot %d is out of bound lastindex(%d)", i, ms.lastIndex()) // <-
	}

	ms.snapshot.Metadata.Index = i
	ms.snapshot.Metadata.Term = ms.ents[i-offset].Term // <- i < offset wraps around
```

etcd does not reach either panic: it calls `CreateSnapshot` only with its applied index, after
waiting for the raft goroutine to persist the entries, and it compacts only below its own last
snapshot, so the index is in range. v3.7.0 has the same code (`storage.go:243-263`).

**Expected**: either documented preconditions (`firstIndex()-1 <= i <= lastIndex()`, as
`Compact` documents its own upper bound: "It is the application's responsibility to not
attempt to compact an index greater than raftLog.applied"), or `ErrCompacted` for a
compacted `i`, as the other methods return.

**How the proof handles it**: `MemoryStorage.CreateSnapshot.spec`
(`Spec/go_etcd_io/raft/v3/MemoryStorage__CreateSnapshot.lean`) takes the premise
`ss.index < i → prev.index ≤ i ≤ prev.index + |ents|`, which makes both panics unreachable.

**Possible fixes**: document the range; or return `ErrCompacted` when `i < offset` (and
keep, or document, the `Panicf` above `lastIndex`).

**Found**: 2026-10-12, specifying `MemoryStorage.CreateSnapshot` (Lean-first).
