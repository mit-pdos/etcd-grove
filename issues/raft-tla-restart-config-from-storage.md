---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/raft#226 pr open: related, reworks the trace specification's restart; keeps restoring the configuration from the durable state
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a restart before the application's first snapshot

A node restarted from its storage takes its configuration from `Storage.InitialState()`'s
`ConfState`, which `MemoryStorage` (etcd's raft storage) holds only in its snapshot, and the
application then applies the committed entries after `Config.Applied` again, configuration changes
included. Before the application's first snapshot, the restarted node therefore starts with an
empty configuration and rebuilds it by re-applying the bootstrap and later configuration entries.
`tla/etcdraft.tla`'s `Restart` instead restores the configuration persisted at the node's last
`Ready`, so trace validation (`tla/validate.sh` with `Traceetcdraft.tla`) rejects the restarted
node's `InitState` line. Raft itself behaves correctly: the restarted node has its persisted term,
vote, commit index and log, and, once its application re-applies its log, its configuration.

**Expected:** a trace of a correct run with a restart should pass `Traceetcdraft.tla`, as
`tla/README.md` describes ("The `StartNode` and/or `RestartNode` should be invoked with `Config`
with `TraceLogger` property set"; a failure "indicates a discrepancy between the model and its
implementation").

**Impact:** at `c51f010` every restart is rejected anyway, for an earlier reason
([`raft-tla-restart-initstate-unmatched`](raft-tla-restart-initstate-unmatched.md)); with that
fixed, a restart is still rejected unless the configuration `InitialState` returns is the one the
node had at its last `Ready`: an application that keeps raft's `MemoryStorage` and its own
snapshots (raft's documented usage) restarts with its last snapshot's configuration and re-applies
the configuration changes after it. etcd mostly avoids it: on restart it builds the snapshot's
`ConfState` from its backend's membership
([`bootstrap.go`](https://github.com/etcd-io/etcd/blob/main/server/etcdserver/bootstrap.go),
`buildConfStateFromV3store`), so raft starts with the configuration applied up to the backend's
consistent index, and only the configuration changes after that index are applied again (not
checked here: whether a change applied before the last `Ready` can be missing from the backend at a
crash). raft v3.7.0 and `main` have the same specification.

**Reproduction:** `TestTLATraceRestartWithoutSnapshot` in
[`issues/raft-tla-restart-config-from-storage/tla_restart_config_test.go`](raft-tla-restart-config-from-storage/tla_restart_config_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding `validate.sh`'s `tla2tools.jar` (nightly 2.0, 2026-11-06) and
`CommunityModules-deps.jar` (as downloaded 2026-11-08). It fails at `c51f010`, at the `InitState`
line (term 0: the earlier finding); with that finding's `fix.patch` applied to `raft.go`, it still
fails at the same line, whose term, vote, commit and log now match and whose configuration does not:

```
$ git apply issues/raft-tla-restart-initstate-unmatched/fix.patch   # raft.go only
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceRestartWithoutSnapshot$' -count=1 -v
    tla_restart_config_test.go:223: Error: Temporal property TraceMatched was violated.
    tla_restart_config_test.go:223: Error: The following behavior constitutes a counter-example:
    tla_restart_config_test.go:226: no behavior matches trace line 76: {"level":"debug","ts":1000000075,"msg":"trace","tag":"trace","event":{"name":"InitState","nid":"2","state":{"term":2,"vote":"1","commit":4},"role":"StateFollower","log":4,"conf":[[],[]]}}
    tla_restart_config_test.go:228: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceRestartWithoutSnapshot (1.76s)
```

The run is `raft-tla-restart-initstate-unmatched`'s without its snapshot: three nodes configured
as `tla/README.md`'s example; node 1 is elected for term 2 and commits its entry at index 4 on every
node; node 2 is restarted (a new `RawNode` on the same `MemoryStorage`, `Applied` 0, as an
application that has taken no snapshot); the test checks it restarted with its term, vote and commit,
re-applies indexes 1 to 4 (three `ApplyConfChange`s) and is back to voters 1, 2, 3, then lets it
answer a heartbeat. (The test fails the same way with every other finding's fix applied as well.)

**Cause:** [`Restart`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L276-L288)
sets `config` to `durableState[i].config`, which
[`PersistState`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L229-L236)
records at every `Ready`; raft persists no configuration of its own
([`newRaft`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L472)
restores `InitialState`'s `ConfState`, which `MemoryStorage` takes from its snapshot). And the
re-applied entries could not be followed either:
[`ApplySimpleConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L464-L475)
applies the last configuration entry at or below the commit index, where raft applies each in turn.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs that restart a node whose storage's configuration is older than its last `Ready`'s (notes/trace-validation-plan.md).

## Fix

No patch. The specification would need what raft restores: the configuration of the storage's
snapshot (the model has no application snapshots; it could record, durably, the configuration and
index an application's snapshot covers), and configuration entries applied one at a time from
there (an applied-configuration index, so that `ApplySimpleConfChange` applies the next
configuration entry rather than the last). Alternatively `tla/README.md` could require applications
to persist their applied configuration with each `Ready` (a `ConfState` that `InitialState`
returns), which `MemoryStorage` offers only through `CreateSnapshot`.

## Notes

Found 2026-11-08 by random runs of the corrected specification
(`examples/raft/tracecheck/tla-fixes/`), whose driver restarted nodes without a snapshot at what
they applied; it now takes one before every restart, as `raft-tla-restart-initstate-unmatched`'s
test does (that write-up's Notes anticipated this mismatch).
