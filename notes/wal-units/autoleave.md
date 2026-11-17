# Unit `autoleave`: the restarted server's `ConfState.AutoLeave` (branch `wal-c-autoleave`)

Brief: specgap row 11 (a) / P5 (conf-state half) says that after a restart the apply thread's
`ep.confState` is `buildConfStateFromV3store`'s `ConfState{Voters, Learners}` with `AutoLeave` nil,
so its first snapshot before any conf change is not canonical, against the SpecPlan's
`confStateFull` and the `fsExt` WAL's `walSnapAt`/`walCsCanon`. The user's decision
(2026-11-15): generalize the specs, do not change Go.

## Session 1 (2026-11-15): the finding is false; nothing generalized, the user's call reopened

### The premise does not hold of the code

`ep.confState` never lacks `AutoLeave`. The restart path (fork `goose-lean-walfs`, raft `565c2bd`):

1. `bootstrap.go:107-115`: `cs := buildConfStateFromV3store(...)` (`AutoLeave` nil);
   `sn.Metadata.ConfState = &cs; s.wal.snapshot = sn`.
2. `bootstrapRaftFromWAL` (`bootstrap.go:571`) → `bwal.MemoryStorage()` (`:741-753`) →
   `s.ApplySnapshot(wal.snapshot)`. raft's `MemoryStorage.ApplySnapshot` (`storage.go:218-237`)
   runs `snap = pb.EnsureSnapshot(snap)` first: `EnsureConfState` stores `AutoLeave = new(false)`
   (in place, through bootstrap's own `cs`), then keeps `proto.Clone(snap)` (proto2: a set `false`
   keeps its presence).
3. `run()` (`server.go:755`): `sn, err := s.r.raftStorage.Snapshot()`; `MemoryStorage.Snapshot`
   (`storage.go:208-214`) runs `EnsureSnapshot(ms.snapshot)` again and returns a `proto.Clone`;
   `ep := etcdProgress{confState: sn.Metadata.ConfState, ...}` (`server.go:803-809`). This is the
   `server.go:804` specgap cites: it reads the `MemoryStorage`'s snapshot, not bootstrap's `cs`.

The other writes of `ep.confState` are full too: `applySnapshot` (`server.go:1175`, the `Ready`'s
snapshot, which raft ensured in `handleSnapshot`/`restore`) and `applyConfChange` (`:2053`,
`node.ApplyConfChange`, i.e. `ProgressTracker.ConfState()`). The apply thread's `snapshot()` passes
it to `CreateSnapshot` (`storage.go:243-262`), which clones it, so the snapshot `SaveSnap` hands the
WAL has `AutoLeave` set. The raft loop's `SaveSnap(rd.Snapshot)` (`raft.go:257`) saves raft's own
snapshot (full). The new-cluster path (`NewMemoryStorage`, `storage.go:119-126`) ensures as well.

Measured (a scratch Go module against the pinned raft, `go.etcd.io/raft/v3 =>`
`upamanyus/etcd/v3@v3.0.0-20261028061729-565c2bda9e6d`):

```go
cs := pb.ConfState{Voters: []uint64{1, 2, 3}}           // buildConfStateFromV3store's
sn := &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: new(uint64(5)), Term: new(uint64(2)), ConfState: &cs}}
s := raft.NewMemoryStorage(); s.ApplySnapshot(sn)       // bwal.MemoryStorage()
got, _ := s.Snapshot()                                  // run(), server.go:755
s.Append([]*pb.Entry{{Index: new(uint64(6)), Term: new(uint64(2))}})
cr, _ := s.CreateSnapshot(6, got.Metadata.ConfState, nil) // snapshot(), server.go:2132
```

prints `bootstrap cs AutoLeave nil: true`, `ep.confState AutoLeave nil: false`,
`CreateSnapshot cs AutoLeave nil: false`.

### Question 1: blind spot, or inconsistency?

Neither, for `AutoLeave`: the SpecPlan's claim that `ep.confState` is a `confStateFull` (realization
of `applyThread`, `ApiApply.lean:51,97`; `raftNode__ApplyConfChange`, `createMergedSnapshotMessage`,
`EtcdServer__snapshot`) is true of the code, on every path including the restart. No two SpecPlan
specs contradict: raft's `Api.lean:98` already says the `MemoryStorage`'s stored snapshot's
`ConfState` is "stored ensured: `AutoLeave` present", `MemoryStorage.Snapshot.spec` returns a
`snapshotPts` (full), and `bootstrap.lean` (trusted) only says the configuration is rebuilt from the
backend, then applied to a `MemoryStorage` (which ensures). The `fsExt` WAL's `walCsCanon`
(`AutoLeave` set) is likewise what the server writes.

What the SpecPlan does miss (a blind spot in the provenance, not in the canonical form):
`applyInit_ep.spec` (`ApiApply.lean:724-732`) produces `applyThread s γ ep p`, whose realization
holds `ep.confState` as a `confStateFull` listing the configuration at the consistent index, from
`applyInit s γ p c` and `ep.confState ↦ cs` for an **arbitrary** `cs`: nothing says `cs` is the
`MemoryStorage` snapshot's conf state (`run`'s step 1 gets its `snapshotPts`, step 5 drops it), nor
that it lists the configuration at `c` (true because bootstrap rebuilt it from the backend, which is
at `c`). As stated the law is unprovable. Ledger entry (proposed, not edited: the fix touches
`applyInit`'s arity or content, i.e. `run`/`start`/`NewServer`, batch 2d/2e's).

Other canonical forms the restart path could break, checked:
- hard state: `walHsCanon` (all three set unless empty) is raft's `hardState()` (`raft.go:504-510`);
  an empty one writes no record. Fine.
- entries: raft's entries keep the proposal's presence (already recorded, U4 b, P5's entry half).
  A restart re-reads entries into the `MemoryStorage` and never rewrites them. Nothing new.
- `walSnapCanon` maps a zero conf-state model to an absent `ConfState`, while a raft snapshot always
  has one (set, possibly empty, `AutoLeave` set). Unreachable for the server (a saved snapshot is at
  an index `> 0`, whose configuration has a voter: `confchange` refuses removing the last), noted.

### What is not done, and why (the user's call)

The decision "generalize the specs, do not insist on `AutoLeave`" was taken on specgap's false
reading. I did not carry it out:
- SpecPlan: generalizing `ep.confState` to any `ConfState` would weaken what the specs already say
  correctly (and what callers use: `CreateSnapshot`'s and the merged `MsgSnap`'s full snapshot), for
  a case the code never reaches. No SpecPlan file changed, so no build was needed.
- `fsExt` WAL: the record's history op `.snap m` holds a model (`SnapshotMetadataM`, presence lost;
  `WalOpG` is in `LinuxFs/GooseLang/Ext/AbsDisk/Impl.lean`) and the bytes are `Mr.encSnap m`. Admitting
  an absent `AutoLeave` means a history over wire contents (P5's representation, already marked
  [user]) or a presence bit in `WalOpG.snap`: every WAL reader proof, `WalHist` (a part copy of a
  main-tree module) and the tester change, overlapping the three concurrent WAL units.

Options for the user:
1. **(recommended)** Withdraw the conf-state half of P5 and specgap 11 (a): the specs stand as they
   are; P5 remains for entries only. Optionally fix `applyInit_ep` (ledger entry below).
2. Generalize the `fsExt` WAL anyway, for clients other than the server: `etcdutl snapshot restore`
   (`etcdutl/snapshot/v3_snapshot.go:573-577`) saves `walpb.Snapshot{ConfState: &raftpb.ConfState{Voters:
   nodeIDs}}`, `AutoLeave` nil. etcdutl is not in the verified scope; this would be done together with
   P5's wire-content representation for entries (one change to `WalOpG`/`Mr`), not separately.
3. Generalize the SpecPlan's `storage.SaveSnap`/`Release` to a snapshot whose conf state is set but
   may lack `AutoLeave` (needs a new raftpb predicate between `snapshotRaw` and `snapshotPts`). The
   only snapshot of that kind in the plan is `examples/specreq/etcdserverboot/storage.go`'s
   `ReqSaveOrder` (`ConfState{Voters: []uint64{1}}`), which is a Go test of a trusted model, not a
   proof obligation; no real caller needs it.

Ledger: two entries of 2026-11-15 (the conf-state half of P5 withdrawn, proposed; `applyInit_ep`'s
provenance, proposed). `notes/wal-units/specgap.md` row 11 (a) and P5 annotated.

No Lean file changed; no `sorry`, no hypothesis added. No Go bug found.
