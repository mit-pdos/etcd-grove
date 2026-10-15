# raft: zero `MaxSizePerMsg` and `MaxCommittedSizePerReady` panic on the first commit

**Status**: open (not reported upstream; not checked whether raft after `40f8be7` fixed it).

**Where** (etcd-io/raft at `40f8be730b18`, the revision `etc/goose.py` pins):

- `raft.go:187-199`: `Config.MaxSizePerMsg`'s documentation: "math.MaxUint64 for
  unlimited, 0 for at most one entry per message". `MaxCommittedSizePerReady` has no
  documented range.
- `raft.go:317-318`: `Config.validate` sets `MaxCommittedSizePerReady = MaxSizePerMsg`
  when it is 0, and accepts 0 for both.
- `raft.go:441`: `newLogWithSize(..., entryEncodingSize(c.MaxCommittedSizePerReady))`, so
  the log's `maxApplyingEntsSize` is 0.
- `log.go:232-235`: `raftLog.nextCommittedEnts`:
  `maxSize := l.maxApplyingEntsSize - l.applyingEntsSize; if maxSize <= 0 { l.logger.Panicf(...) }`.

**What happens**: with both fields 0 (their zero values), the first `Ready` that has an
entry to apply panics ("applying entry size (0-0)=0 not positive"), from
`RawNode.Ready` → `readyWithoutAccept` → `nextCommittedEnts`. Reproduction (a single-voter
cluster; the first `Ready` already panics, on the conf change entry at index 1 that
`Bootstrap` marks committed, before any `Campaign`):

```go
func TestZeroSizes(t *testing.T) {
	s := raft.NewMemoryStorage()
	rn, err := raft.NewRawNode(&raft.Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1,
		Storage: s, MaxInflightMsgs: 256})
	if err != nil {
		t.Fatal(err)
	}
	_ = rn.Bootstrap([]raft.Peer{{ID: 1}})
	for i := 0; i < 5; i++ {
		if rn.HasReady() {
			rd := rn.Ready() // panics at log.go:234
			s.Append(rd.Entries)
			rn.Advance(rd)
		}
		_ = rn.Campaign()
	}
}
```

Run on 2026-10-11 against `go.etcd.io/raft/v3@40f8be730b18`: panics at `log.go:234`.

**How it happens**: `validate` copies `MaxSizePerMsg` into `MaxCommittedSizePerReady` when the
latter is 0, so with both at 0 the log's apply budget `maxApplyingEntsSize` starts at 0.
`nextCommittedEnts` treats an exhausted budget while applying is not paused as an invariant
violation. Applying is paused only once some entries are outstanding, so the first `Ready` with
a committed entry reaches the `Panicf`. The test above runs:

1. `NewRawNode` with both fields 0: `validate` sets `MaxCommittedSizePerReady = 0`, and
   `newRaft` builds the log with `maxApplyingEntsSize = 0`, `applyingEntsSize = 0`.
2. `Bootstrap([{ID: 1}])` appends the conf change adding node 1 at index 1 and marks it
   committed.
3. `HasReady()` is true, and the first `Ready()` (before any `Campaign`) calls
   `nextCommittedEnts`: applying is not paused, index 1 is to be applied, and
   `maxSize = 0 - 0 = 0`, so it panics with "applying entry size (0-0)=0 not positive".

```go
// raft.go:315-319 and 441 (etcd-io/raft 40f8be7)
	// default MaxCommittedSizePerReady to MaxSizePerMsg because they were
	// previously the same parameter.
	if c.MaxCommittedSizePerReady == 0 {
		c.MaxCommittedSizePerReady = c.MaxSizePerMsg // <- 0 stays 0
	}
	// ... (newRaft)
	raftlog := newLogWithSize(c.Storage, c.Logger, entryEncodingSize(c.MaxCommittedSizePerReady))
```

```go
// log.go:218-237 (etcd-io/raft 40f8be7)
func (l *raftLog) nextCommittedEnts(allowUnstable bool) (ents []pb.Entry) {
	if l.applyingEntsPaused {
		// Entry application outstanding size limit reached.
		return nil
	}
	// ...
	lo, hi := l.applying+1, l.maxAppliableIndex(allowUnstable)+1 // [lo, hi)
	if lo >= hi {
		// Nothing to apply.
		return nil
	}
	maxSize := l.maxApplyingEntsSize - l.applyingEntsSize // <-
	if maxSize <= 0 {
		l.logger.Panicf("applying entry size (%d-%d)=%d not positive", // <-
			l.maxApplyingEntsSize, l.applyingEntsSize, maxSize)
	}
```

etcd does not reach it: it sets `MaxSizePerMsg` to 1 MiB (`maxSizePerMsg`,
`server/etcdserver/raft.go:38`) and leaves `MaxCommittedSizePerReady` at 0, which `validate`
defaults to 1 MiB. The code is the same in raft v3.7.0.

**Expected**: a configuration `validate` accepts, with `MaxSizePerMsg = 0` documented as
"at most one entry per message", should run; by analogy applying should proceed one entry
at a time.

**How the proof handles it**: `newRaft`'s spec takes the premise
`MaxCommittedSizePerReady ≠ 0 ∨ MaxSizePerMsg ≠ 0` (`Spec/go_etcd_io/raft/v3/newRaft.lean:120`,
explained in the comment above it), carried by `NewRawNode`/`RestartNode`; with it the panic
is unreachable (`Hpaused`, `Proof/go_etcd_io/raft/v3/InvRaftlog.lean:508`). The verified results
say nothing about the zero configuration: the premise is stronger than raft's API states.

**Possible fixes**: `validate` rejects `MaxCommittedSizePerReady = 0` after defaulting (or
defaults it to a nonzero value); or `nextCommittedEnts` applies at least one entry when the
budget is exhausted from zero, matching `MaxSizePerMsg`'s "at most one entry" meaning.

**Found**: 2026-10-11, by a sweep classifying raft's panic sites against the proof (the
premise had been added earlier when proving `nextCommittedEnts`), confirmed with the test
above.
