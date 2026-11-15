# kvraftN: handoff

Scope: `notes/kvraftN-scope.md`; decisions (etcd-grove-81, 2026-11-15): kv as `MainN(k)` with `Main() = MainN(3)`,
the spec over a voter list kept in `RKVNames`, new `raft_kvN_porcupine_safe`, `raft_kv_porcupine_safe`'s text unchanged;
kvreconf then kvdurable as R2 (`MainN(k)`, `max = k + 4`, existing theorems unchanged); `B = 1000`; names
`raft_kvN_porcupine_safe`, `raft_kvreconfN_porcupine_safe`, `raft_kvdurableN_porcupine_safe`. Each closed statement
goes to the user before linking (hard stop).

## Done (kv, up to the linking stop)

- Go: `examples/raft/kv/check.go` `MainN(k uint64)` (voters `1 … k`, `StartCluster`, `Check(…, 4, 25)`), `Main()` =
  `MainN(3)`; `kv_test.go` `TestMainN` (k from {1, 3, 5, 7}, `KV_MEMBERS` overrides, 1..1000); `cmd/kvcheck -members k`.
  Translated (`etc/goose.py --project kv`). 20 runs of `TestMainN` under 32G: all ok (k = 1 ×6, 3 ×9, 7 ×5), and
  `KV_MEMBERS=5` once.
- Lean: `KvVotersOk` and `RKVNames.voters`/`votersOk` (`Defs.lean`); `kvVoters` gone, `kvMembership γr`; `rkvInv_alloc`,
  `kvCluster_alloc` take `vs` and `KvVotersOk vs`; `kvConfState_is γr`; `KV__run`'s snapshot lists from `γr.votersOk`;
  `StartCluster.spec` over `vs` (`KvVotersOk vs`, `rs.length = vs.length`) and its proof; `MainN.spec` (`1 ≤ k < 2^62`)
  and its proof (`kvBootVoters`, `kvBootVoters_ok`, `kvBootVoters_snoc`, `MainN.lean`); `Main.wp_proof` from `wp_MainN`.
  Every kv module but `Link`, `Results`, `Adequacy*` builds.

## Next, in order

1. (after the user approves `raft_kvN_porcupine_safe`) `etc/link-lean-first-kv.txt`: `kv_MainN: kv_StartCluster kv_Check
   CounterClock`, `kv_Main: kv_MainN`; regenerate `Link.lean` (`etc/gen-link.py --kv`). Until then `Link.lean` does not
   build (it calls `Main.wp_proof` with the old callees).
2. `Adequacy.lean`: `kvMainNSpec`, `kvProgramN k`, `kvN_adequate_of`; `AdequacyLinked.lean`: `raft_kvN_adequate`;
   `Results.lean`: `kv_MainN`, `raft_kvN_porcupine_safe`, the `StartCluster`/alloc docstrings (voters `vs`);
   `etc/tcb-collections/kv.txt` roots; full build, gates.
3. kvreconf (R2), its stop; kvdurable (R2), its stop.

## Open observations

- kvdurable at k = 7 (today's `maxReplicas = 9`, `Run(RandomConfig())` with `Voters = 7`) took 15 minutes once (k = 1, 3:
  20 s, 15 s); performance, not safety. kvdurable's Go test draws k from {1, 3, 5}.

## Pitfalls

- Keep voter lists symbolic: no `decide` on `kvBootVoters k`, no bare `iframe` over `[∗list]` of them.
- `γr.voters = vs` comes out of `kvCluster_alloc` as `Hγv`; rewrite with it where a definition unfolds to `γr.voters`
  (`runStor`, `kvConfState_is γr`) rather than `subst` (which would erase `vs`).
- Builds: `lake --packages=/shared/tmp/manifest-e9e.json build …` under `systemd-run --scope -p MemoryMax=64G` (full builds
  also under `flock /shared/tmp/etcd-grove-build.lock`); Go with GOWORK=off and the 32G cap.
