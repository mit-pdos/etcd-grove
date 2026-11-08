---
upstream: none
checked: 2026-11-08
links: []
blocks-proof: yes
---

# raft: TLA+ model checking fails evaluating `Restart` after a conflicting append request

`tla/etcdraft.tla` handles a conflicting append request in steps: `ConflictAppendEntriesRequest`
drops the follower's last entry, and later steps append. In between, the follower's log is shorter
than its persisted length (`durableState[i].log`, a number), and `Restart(i)`, enabled in every
state, takes `SubSeq(log[i], 1, durableState[i].log)` past the log's end, so TLC stops with "The
third argument of SubSeq must be in the domain of its first argument" whenever it evaluates `Next`
in such a state.

**Expected:** the specification's next-state relation should be defined in every state it reaches,
and a restart should restore what was persisted, as raft does (a restarted node reads its log from
`Storage`, which still holds the entries a truncation had not yet removed from it).

**Impact:** model checking with crashes (`Next` includes `NextCrash`, as in `MCetcdraft.cfg`'s
`NextDynamic`) aborts with an evaluation error as soon as it reaches a conflicting append request,
instead of exploring restarts there. Trace validation is not affected (`Traceetcdraft` takes
`Restart` only at an `InitState` line). raft v3.7.0 and `main` have the same specification.

**Reproduction:** `TestTLAModelRestartAfterTruncation` in
[`issues/raft-tla-restart-truncated-log/tla_restart_truncated_log_test.go`](raft-tla-restart-truncated-log/tla_restart_truncated_log_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding what `validate.sh` downloads (`tla2tools.jar`, nightly 2.0
2026-11-06, and `CommunityModules-deps.jar`, as of 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLAModelRestartAfterTruncation$' -count=1 -v
    tla_restart_truncated_log_test.go:426: replay: Error: The third argument of SubSeq must be in the domain of its first argument:
    ...
    tla_restart_truncated_log_test.go:60: etcdraft.tla's Next cannot be evaluated in a state it reaches: The third argument of SubSeq must be in the domain of its first argument: (evaluating Next in replayed state 212 of 243)
--- FAIL: TestTLAModelRestartAfterTruncation (6.15s)
```

The test reaches a conflicting append request through a run of raft: five `RawNode`s with
`MaxSizePerMsg` 1, where node 4's entry of term 3 at index 6 is replaced by the term-4 leader's entry
of term 2 (the run of `raft-tla-more-up-to-date-cut-batches`). It replays the states of
`Traceetcdraft`'s counterexample on that run, the specification's variables only, against
`MCetcdraft.tla` from its `Init` (each step a `NextAsync` action or a stutter onto the next recorded
state), while TLC also evaluates the whole of `Next` in each state reached: at state 212, between
the truncation and the append, `Restart`'s `SubSeq` fails.

**Cause:** [`Restart`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L276-L288)
restores the log as a prefix of the in-memory log of the persisted length, which assumes the
in-memory log never shrinks below what was persisted;
[`ConflictAppendEntriesRequest`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L587-L591)
shrinks it without persisting.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) relies on etcdraft.tla being a sound model of raft, which cannot be model-checked with restarts past a conflicting append request (notes/trace-validation-plan.md).

## Fix

[`fix.patch`](raft-tla-restart-truncated-log/fix.patch): the durable state keeps the persisted log
itself, not its length (`PersistState`, `InitDurableState`), `Restart` restores it, and
`CommittedIsDurableInv` compares with its length. With it the test passes at `c51f010` (checked
2026-11-08), and the two trace tests of `raft-tla-leader-completeness-stale-leader` and
`raft-tla-more-up-to-date-cut-batches` still fail as before (their invariants), not earlier.
