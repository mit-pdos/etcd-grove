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
cluster, which commits its own empty entry once it elects itself):

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
