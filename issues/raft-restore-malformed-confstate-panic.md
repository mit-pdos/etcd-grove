---
upstream: unchecked
checked: 2026-11-02
links:
---

# raft: a node restarted from a malformed `ConfState` panics in `newRaft`

**Status**: an unstated precondition (not a bug in raft's own use). `Storage.InitialState`'s
`ConfState` must be well-formed, and raft's API does not say so. Found by the durability proof
(stage II(r), `newRaft.spec`'s new premise `ConfStateOk`).

**Where**: `raft.go`, `newRaft` (lines 472–479 in the checkout at `509271dac8a4`; the pinned
revision is the fork's `565c2bd`, `etc/goose.py`). It calls `confchange.Restore` on the
`ConfState` that `Storage.InitialState` returns, then
`assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))`, which panics through the
logger when the restored configuration does not round-trip to `cs`. The documentation of
`Storage.InitialState` and `Config.Storage` says nothing about the `ConfState`'s form.

**What triggers it**: a `ConfState` that `Restore` accepts but that does not round-trip:

- a repeated id, for example `Voters: [1, 1]`. The restored configuration has `Voters: [1]`, and
  `ConfState.Equivalent` compares the sorted lists `[1, 1]` and `[1]`;
- `AutoLeave: true` with no `VotersOutgoing`. The restored configuration is not joint, so it
  carries no auto-leave.

**Reproduction** (not yet run): a `MemoryStorage` whose snapshot metadata holds one of these
`ConfState`s, then `NewRawNode(&Config{ID: 1, Storage: s, ...})`. The expected result is a panic
in `assertConfStatesEquivalent`.

**Impact**: a client whose storage hands back a hand-built or corrupted `ConfState` crashes at
restart instead of getting an error. etcd's own `ConfState`s come from raft (`ApplyConfChange`),
so they are well-formed.

**Fix options**: document the precondition on `Storage.InitialState` (the `ConfState` must be one
that raft produced, or at least free of repeated ids, with `AutoLeave` only when joint), or have
`newRaft` return or log an error for one that does not round-trip.

**In the proof**: `newRaft.spec` and `NewRawNode.spec` take `ConfStateOk csm`. `RestartNode`
obtains it from the storage's `confStateIs`/`memValid`, so the node API is unchanged.
