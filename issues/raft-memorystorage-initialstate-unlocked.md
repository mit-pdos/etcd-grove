# raft: `MemoryStorage.InitialState` accesses its fields without the mutex

**Status**: open (not reported upstream). **Also in raft v3.7.0** (2026-10-15, the retarget's
inventory): `storage.go:128-134` still takes no lock, and now also *writes*: `pb.EnsureConfState(cs)`
sets the stored snapshot's `ConfState.AutoLeave` when it is nil (`raftpb/util.go:20-28`), and
returns `ms.hardState` and that `ConfState` uncloned (the caller shares them with the storage).

**Where** (etcd-io/raft at `40f8be730b18`, the revision `etc/goose.py` pins):

- `storage.go:98-101`: `MemoryStorage`'s `sync.Mutex`: "Protects access to all fields. Most
  methods of MemoryStorage are run on the raft goroutine, but Append() is run on an
  application goroutine."
- `storage.go:121-124`: `InitialState` increments `ms.callStats.initialState` and reads
  `ms.hardState` and `ms.snapshot.Metadata.ConfState` without taking the lock, while
  `SetHardState`, `ApplySnapshot` and `CreateSnapshot` write those fields under it.

**What happens**: a data race whenever `InitialState` runs concurrently with one of those
writers (e.g. the application calling `SetHardState` on its goroutine while a node is
being created on another). Reproduction (in package `raft`,
`go test -race -run TestMemoryStorageInitialStateRace`; the race detector reports the
read at `storage.go:123` against the write in `SetHardState`):

```go
func TestMemoryStorageInitialStateRace(t *testing.T) {
	ms := NewMemoryStorage()
	done := make(chan struct{})
	go func() {
		for i := uint64(0); i < 1000; i++ {
			_ = ms.SetHardState(pb.HardState{Term: i})
		}
		close(done)
	}()
	for i := 0; i < 1000; i++ {
		_, _, _ = ms.InitialState()
	}
	<-done
}
```

In raft's own use `InitialState` is called once, from `newRaft`, before any `Ready` is
handed to the application, so raft itself does not race; the issue is the method against
its type's documentation.

**Expected**: `InitialState` takes the lock like every other exported method, or the
documentation says it must not run concurrently with the writers.

**How the proof handles it**: the lock's invariant holds only half of `hardState` and of
`snapshot`, and not the `initialState` counter; the other halves and the counter are
`memStorMeta` (`Proof/go_etcd_io/raft/v3/InvMemstorage.lean`), which `InitialState`'s spec
takes and the writers' specs need too, so they cannot run concurrently
(`Spec/go_etcd_io/raft/v3/MemoryStorage__InitialState.lean`).

**Possible fixes**: `ms.Lock(); defer ms.Unlock()` in `InitialState`.

**Found**: 2026-10-12, specifying `MemoryStorage.InitialState` (Lean-first).
