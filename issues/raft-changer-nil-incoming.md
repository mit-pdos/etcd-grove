---
upstream: unchecked
checked:
links:
---

# raft: a `confchange.Changer` over a tracker with a `nil` incoming voter map panics

**Status**: open (not reported upstream; minor: raft's own trackers never have it).

**Where** (etcd-io/raft at `40f8be730b18`, the revision `etc/goose.py` pins):

- `confchange/confchange.go:29-35`: `Changer` is exported, with an exported `Tracker`
  field; nothing documents that `Tracker.Voters[0]` must be a non-`nil` map.
- `confchange/confchange.go:178-189` (`makeVoter`) and `:247-250` (`initProgress`):
  `incoming(cfg.Voters)[id] = struct{}{}` writes into the copy of `Voters[0]`, which
  `Config.Clone` leaves `nil` when the original is `nil`.
- `checkInvariants` accepts a `nil` `Voters[0]`.

**What happens**: a `Changer` over a zero `tracker.ProgressTracker` (or any tracker whose
`Voters[0]` is `nil`) panics with "assignment to entry in nil map" on the first `AddNode`:

```go
func TestNilIncomingPanics(t *testing.T) {
	defer func() {
		if r := recover(); r == nil {
			t.Fatal("expected a panic")
		}
	}()
	c := Changer{Tracker: tracker.ProgressTracker{Progress: tracker.ProgressMap{}, MaxInflight: 10},
		LastIndex: 1}
	_, _, _ = c.Simple(pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeId: 1})
	// panics: assignment to entry in nil map
}
```

`tracker.MakeProgressTracker` builds `Voters[0]` as an empty non-`nil` map, so raft itself
never reaches this.

**How it happens**: adding a voter writes into the incoming voter map without allocating it,
unlike the learner sets, which go through `nilAwareAdd`. In the test above:

1. The tracker is a literal with `Voters[0] == nil` (and `Voters[1] == nil`).
2. `Simple(AddNode 1)` copies the configuration with `checkAndCopy`, whose `Config.Clone`
   keeps the `nil` map, and `checkInvariants` accepts it.
3. Node 1 has no progress, so `makeVoter` calls `initProgress`, which runs
   `incoming(cfg.Voters)[1] = struct{}{}` on the `nil` map: "assignment to entry in nil map".

```go
// confchange/confchange.go:178-189 and 247-252 (etcd-io/raft 40f8be7)
func (c Changer) makeVoter(cfg *tracker.Config, trk tracker.ProgressMap, id uint64) {
	pr := trk[id]
	if pr == nil {
		c.initProgress(cfg, trk, id, false /* isLearner */)
		return
	}

	pr.IsLearner = false
	nilAwareDelete(&cfg.Learners, id)
	nilAwareDelete(&cfg.LearnersNext, id)
	incoming(cfg.Voters)[id] = struct{}{} // <-
}

func (c Changer) initProgress(cfg *tracker.Config, trk tracker.ProgressMap, id uint64, isLearner bool) {
	if !isLearner {
		incoming(cfg.Voters)[id] = struct{}{} // <-
	} else {
		nilAwareAdd(&cfg.Learners, id)
	}
	// ...
```

etcd never uses `confchange` directly, so it does not reach this. The code is the same in raft
v3.7.0.

**Expected**: either a documented precondition (build the tracker with
`MakeProgressTracker`), or `makeVoter`/`initProgress` allocating the map as `nilAwareAdd`
does for the learner sets.

**How the proof handles it**: the representation predicate `ownCfgCC`
(`Proof/go_etcd_io/raft/v3/InvConfchange.lean`) requires the incoming voter map to be a map
(`vin ↦${dq} c.incoming`), so every `confchange` spec assumes it.

**Possible fixes**: document the precondition; or allocate a `nil` `Voters[0]` in
`checkAndCopy`/`initProgress`.

**Found**: 2026-10-12, while generalizing the `confchange` specs.
