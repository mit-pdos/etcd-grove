# kvraftN: handoff

## START HERE (2026-11-16, etcd-grove-02's kvraftN agent)

Branch `kvraftN`, worktree `/shared/etcd-grove-restartN`. Scope: `notes/kvraftN-scope.md` (R2 for kvreconf, kvdurable;
`B = 1000`; each closed statement goes to the user before linking).

Done:
- kv: linked, landed on lean (`630c6c7b14` … `e9f67cdb20`; `raft_kvN_porcupine_safe` approved 2026-11-16).
- kvreconf up to linking (`18296d64f7`): Go `Options.MaxReplicas` (`RandomOptions`: 9), `RandomOptionsN`/`RandomConfigN`/
  `MainN(k)` (k voters, `k + 4` replicas), `TestMainN` (`KVRECONF_MEMBERS`); Lean `OptsOk` over `MaxReplicas`,
  `freshIdsM`, specs and proofs of `RandomOptionsN`, `RandomConfigN`, `MainN` (`1 ≤ k < 2^59`). Every kvreconf and
  kvdurable module but `Link`/`Results`/`Adequacy*` builds (verified 2026-11-16, targets `/shared/tmp/kvraftN/targets.txt`).
  `TestMainN` 20 runs at 18296d64f7: all PASS (k = 1 ×4, 3 ×6, 5 ×4, 7 ×6; 1.5 to 15 s each) (`/shared/tmp/kvraftN/kvreconf-runs20.txt`, logs `run<i>.log`).
- Draft of `raft_kvreconfN_porcupine_safe`: `notes/kvreconfN-draft.md` (Lean text and plain reading). **Waiting for the
  user's approval (via etcd-grove-02).**

Next, in order:
1. After approval: `kvreconfProgramN`, `kvreconfN_adequate_of` (`Adequacy.lean`, as kv's `kvN_adequate_of`),
   `raft_kvreconfN_adequate` (`AdequacyLinked.lean`), the closed theorem (`Results.lean`, the draft's text);
   `etc/gen-link.py` for kvreconf; tcb `--check` (kvreconf collection unchanged), interfaces, bounds; STATUS entry; ask
   the coordinator before `etc/land.sh`.
2. kvdurable (R2) up to its statement stop (scope: ids `≤ max` in five specs, `kdFileNames_nodup` by `decimalB_inj`,
   the files premise over `1 … k + 4`; draw its test k from {1, 3, 5}: k = 7 once took 15 min).

Pitfalls:
- Builds: `lake --packages=/shared/tmp/manifest-e9e.json build $(cat /shared/tmp/kvraftN/targets.txt)` under
  `systemd-run --scope -q -p MemoryMax=64G` (full builds also under `flock /shared/tmp/etcd-grove-build.lock`).
- Go: `/shared/tmp/kvraftN/runs20.sh` (GOWORK=off, 32G cap; ~6 s a run); run it in the background.
- Keep voter lists symbolic (no `decide` on `bootVoters k`, no bare `iframe` over their `[∗list]`).
- `raft_kvreconf_porcupine_safe`'s text must stay unchanged (`Main()` sets `MaxReplicas = 9`).

## History

Scope: `notes/kvraftN-scope.md`; decisions (etcd-grove-81, 2026-11-15): kv as `MainN(k)` with `Main() = MainN(3)`,
the spec over a voter list kept in `RKVNames`, new `raft_kvN_porcupine_safe`, `raft_kv_porcupine_safe`'s text unchanged;
kvreconf then kvdurable as R2 (`MainN(k)`, `max = k + 4`, existing theorems unchanged); `B = 1000`; names
`raft_kvN_porcupine_safe`, `raft_kvreconfN_porcupine_safe`, `raft_kvdurableN_porcupine_safe`. Each closed statement
goes to the user before linking (hard stop).

### Done (kv, up to the linking stop)

- Go: `examples/raft/kv/check.go` `MainN(k uint64)` (voters `1 … k`, `StartCluster`, `Check(…, 4, 25)`), `Main()` =
  `MainN(3)`; `kv_test.go` `TestMainN` (k from {1, 3, 5, 7}, `KV_MEMBERS` overrides, 1..1000); `cmd/kvcheck -members k`.
  Translated (`etc/goose.py --project kv`). 20 runs of `TestMainN` under 32G: all ok (k = 1 ×6, 3 ×9, 7 ×5), and
  `KV_MEMBERS=5` once.
- Lean: `KvVotersOk` and `RKVNames.voters`/`votersOk` (`Defs.lean`); `kvVoters` gone, `kvMembership γr`; `rkvInv_alloc`,
  `kvCluster_alloc` take `vs` and `KvVotersOk vs`; `kvConfState_is γr`; `KV__run`'s snapshot lists from `γr.votersOk`;
  `StartCluster.spec` over `vs` (`KvVotersOk vs`, `rs.length = vs.length`) and its proof; `MainN.spec` (`1 ≤ k < 2^62`)
  and its proof (`kvBootVoters`, `kvBootVoters_ok`, `kvBootVoters_snoc`, `MainN.lean`); `Main.wp_proof` from `wp_MainN`.
  Every kv module but `Link`, `Results`, `Adequacy*` builds.

### Linked (2026-11-16)

`raft_kvN_porcupine_safe` approved by the user (2026-11-16, via etcd-grove-81); linked (`Link.lean`, `kvProgramN`,
`kvN_adequate_of`, `raft_kvN_adequate`, `Results.lean`); lean `bc64cbfc5e` merged; full build ok; tcb `--check` ok (870, 4),
kv collection unchanged (13 axioms, 0 sorries); mode ok; interfaces ok; STATUS entry. Blocking the land: bounds 364 vs
363 (`MainN.spec`'s `receiptBound`, as `Main.spec`'s), waiting for etcd-grove-81's decision (then
`etc/bounds-check.py --check --update`, land with `etc/land.sh`).

### Next, in order (then)

1. Bounds decision, land kv (`LAKE_PACKAGES=/shared/tmp/manifest-e9e.json PERENNIAL_CHECKOUT=/shared/perennial-e9e6351d9
   etc/land.sh`, GOWORK unset).
2. kvreconf (R2) up to its statement stop; then kvdurable (R2), its stop.

### Open observations

- kvdurable at k = 7 (today's `maxReplicas = 9`, `Run(RandomConfig())` with `Voters = 7`) took 15 minutes once (k = 1, 3:
  20 s, 15 s); performance, not safety. kvdurable's Go test draws k from {1, 3, 5}.

### Pitfalls

- Keep voter lists symbolic: no `decide` on `kvBootVoters k`, no bare `iframe` over `[∗list]` of them.
- `γr.voters = vs` comes out of `kvCluster_alloc` as `Hγv`; rewrite with it where a definition unfolds to `γr.voters`
  (`runStor`, `kvConfState_is γr`) rather than `subst` (which would erase `vs`).
- Builds: `lake --packages=/shared/tmp/manifest-e9e.json build …` under `systemd-run --scope -p MemoryMax=64G` (full builds
  also under `flock /shared/tmp/etcd-grove-build.lock`); Go with GOWORK=off and the 32G cap.
