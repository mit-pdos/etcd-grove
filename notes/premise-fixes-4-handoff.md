# premise-fixes-4: handoff

Branch `premise-fixes-4` (worktree `/shared/etcd-grove-pf4`, off lean `d33293fe11`), session agent
of etcd-grove-81. Brief: fix the round-2 premise attack's findings on `etcd_partition_safe`
(`/shared/tmp/coord-81/round2/findings.json`). Scratch: `/shared/tmp/premise-fixes-4/`.

Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build
--packages=/shared/tmp/manifest-ddc.json`. Go tests: `cd examples; GOWORK=off go test ./premisefix/...`
(under `systemd-run --scope -q -p MemoryMax=32G`).

## Done

1. **rnSetLoggerOk** (critical; decided by etcd-grove-81: prove it). Raft's `isInitialized`
   (`Proof/go_etcd_io/raft/v3/Base.lean`) gains `"#HloggerMu" ∷ sync.isMutex (globalAddr raftLoggerMu)
   (∃ l, globalAddr raftLogger ↦ l)`; raft's `Init.lean` (hand-written: raft is `RAFT_INIT`, external
   to `etc/gen-init.py`) makes the mutex from the two allocations it used to drop. `SetLogger.spec`
   (`{{ isPkgInit raft }} SetLogger l {{ True }}`) proved (`Proof/go_etcd_io/raft/v3/SetLogger.lean`),
   in `etc/api/raft.txt` and raft's Link; `newRaftNode.wp_proof` takes it as a callee (server Link).
   `rnSetLoggerOk` deleted; dropped from `newRaftNode`/`bootstrappedRaft.newRaftNode`/`NewServer`'s
   specs, `NodeStart`, `etcdstart.commonPremises`, `OneMember`, putget3/auth/leaseexpiry's bags and
   every `icases Hprem` pattern.
2. Go tests for fixes 3-5 (`examples/premisefix/{httpmux,httppath,fmtarg}`), passing at go1.27.3.

## Next, in order

- checkpoint (a): report fix 1 + the sweep table (fix 2); stop.
- fixes 3-5: restatements to the coordinator (checkpoint (b)), then implement.
- fix 6 (docstrings), interfaces, tcb + collections, gates, checkpoint (c).

## Pitfalls

- `isInitialized` changed: the whole repository rebuilds.
- `notes/status-history.md` is append-only.
