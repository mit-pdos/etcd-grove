# kvraftN: handoff

## START HERE (2026-11-16, etcd-grove-02's replacement kvraftN agent)

Branch `kvraftN`, worktree `/shared/etcd-grove-restartN`. Scope: `notes/kvraftN-scope.md` (R2; `B = 1000`).
The stage's last part, kvdurable, is linked; what is left is landing it.

Done:
- kv, kvreconf: landed (lean `e9f67cdb20`, `5d2a12df97`).
- kvdurable: `raft_kvdurableN_porcupine_safe` approved (user, 2026-11-16, via etcd-grove-02; Q9) and linked
  (`0286152792`: `MainN` linked, `kvdurableProgramN`, `raft_kvdurableN_adequate`, `Results.lean`); lean merged (`9bc869c902`);
  STATUS entry (`481ff6f024`).
- Go: `TestMainN` runs 1-7 PASS, run 8 (k = 3, `MaxInflightMsgs 1`, `MaxSizePerMsg 0`) hit the 60-min timeout
  (`notes/kvdurableN-draft.md`, Evidence); liveness, decided by etcd-grove-02. Runs 9-20 were killed with the old session.
- Forced-options comparison (Q9's "confirm not new": run 8's options through `Main`'s path vs `MainN(3)`), one run each in
  parallel from 14:44 UTC (`/shared/tmp/kvraftN/forced/forced2.sh`, binary `kvdurable-forced.test`; its source, a temporary
  `zz_forced_test.go`, is not kept): both paths timed out at 2 h (one run each; not new with `MainN`); `forced2.txt`.
- Full build at `481ff6f024` ok; `etc/gates.sh`: all ok but bounds 379 vs 378 (kvdurable `MainN.spec`'s `receiptBound`,
  accepted in advance, Q9), recorded (`etc/bounds-check.py --check --update`); tcb 877/4 and mode 453 unchanged.

Next, in order:
1. Land, only on etcd-grove-02's go (merge lean first if it moved):
   `LAKE_PACKAGES=/shared/tmp/manifest-e9e.json PERENNIAL_CHECKOUT=/shared/perennial-e9e6351d9 etc/land.sh` (GOWORK unset).

Pitfalls:
- Builds (full or targeted): `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build [TARGET...]`
  (common rules, "Memory: two build slots"; no extra flock/systemd-run; exit 143: retry once, then report). Gates:
  `flock /shared/tmp/etcd-grove-full-build.lock` with `LAKE_PACKAGES=... PERENNIAL_CHECKOUT=...`, GOWORK unset.
- lean-check: `--max-open 2`, `--stop` before builds and at the end of a turn; `free -g` ≥ 30 GB available first.
- `.lake/packages` links only iris, batteries, Qq (a stray perennial copy was moved to `/shared/tmp/kvraftN/perennial-aside`).
- Go: GOWORK=off, 32G cap, in the background; kvdurable k = 5 runs take ~6 min, some option draws far longer.
- Keep voter lists symbolic (no `decide` on boot voter lists, no bare `iframe` over their `[∗list]`).
- `Scratch/` (untracked): the old session's probes (`KdNDraft.lean` = `/shared/tmp/kvraftN/KdNDraft.lean`); not built.

## History

### Earlier START HERE (kvdurable to the approval stop)

Branch `kvraftN`, worktree `/shared/etcd-grove-restartN`. Scope: `notes/kvraftN-scope.md` (R2 for kvreconf, kvdurable;
`B = 1000`; each closed statement goes to the user before linking).

Done:
- kv: `raft_kvN_porcupine_safe` landed (lean `e9f67cdb20`). kvreconf: `raft_kvreconfN_porcupine_safe` approved and
  landed (lean `5d2a12df97`; 20/20 `TestMainN`, `notes/kvreconfN-draft.md`).
- kvdurable up to linking (`905bdd96cb`): Go `Options.MaxReplicas` (`RandomOptions`: 9), `RandomOptionsN`/
  `RandomConfigN`/`MainN(dir, k)`, `TestMainN` k from {1, 3, 5} (`KVDURABLE_MEMBERS`), `kvdurablecheck -members`;
  Lean `KdNames.max` (the replica bound, tied to `opts.MaxReplicas` in `isClusterC`), `kdOptsOk` as `OptsOk`,
  `freshIdsM γ.max` in `readSeqsInv`/`clusterLockInv`/`StartCluster`, ids `≤ γ.max` in `isReplica` and the
  `start`/`newReplica`/`readSeqs.next` specs, `Run`'s files over `1 … cfg.MaxReplicas`, `kdFileNamesM_nodup` by
  `decimalB_inj`; specs and proofs of `RandomOptionsN`, `RandomConfigN`, `MainN` (`1 ≤ k < 2^59`, files of
  `1 … k + 4` absent). Every kvdurable module builds, the existing `Results` too (`Main.spec` unchanged).
  `TestMainN` runs: 1-7 PASS, **run 8 (k = 3) hit go test's 60-min timeout** (`notes/kvdurableN-draft.md`, Evidence).
- Draft of `raft_kvdurableN_porcupine_safe`: `notes/kvdurableN-draft.md` (its adequacy from `MainN.spec` checked
  in `Scratch/KdNDraft.lean`, untracked; copy `/shared/tmp/kvraftN/KdNDraft.lean`). **Waiting for the user's approval (via etcd-grove-02).**

Next, in order:
1. After approval: as kvreconf's `da91401f22`: `etc/link-lean-first-kvdurable.txt` (+ `MainN`, `RandomConfigN`,
   `RandomOptionsN`), `etc/gen-link.py --kvdurable`, the draft's `kvdurableProgramN`/`kdMainNSpec`/
   `kvdurableN_adequate_of` (`Scratch/KdNDraft.lean`) into `Adequacy.lean`, `raft_kvdurableN_adequate`,
   `Results.lean`; merge lean; full build; gates (under `flock /shared/tmp/etcd-grove-full-build.lock`); bounds
   (expect +1, `MainN.spec`'s `receiptBound`); STATUS entry; ask the coordinator before `etc/land.sh`.

Pitfalls:
- Builds: `lake --packages=/shared/tmp/manifest-e9e.json build $(cat /shared/tmp/kvraftN/targets.txt)` under
  `systemd-run --scope -q -p MemoryMax=64G` (full builds also under `flock /shared/tmp/etcd-grove-build.lock`; `etc/gates.sh` under `flock
  /shared/tmp/etcd-grove-full-build.lock`).
- Go: `/shared/tmp/kvraftN/runs20.sh` (kvreconf, ~6 s a run), `kd-runs20.sh` (kvdurable: k = 5 takes ~6 min); GOWORK=off,
  32G cap; run them in the background.
- Keep voter lists symbolic (no `decide` on `bootVoters k`, no bare `iframe` over their `[∗list]`).
- The existing closed theorems keep their text (`Main()` sets `MaxReplicas = 9`).

### kv and kvreconf (2026-11-16)

- kv: linked, landed on lean (`630c6c7b14` … `e9f67cdb20`; `raft_kvN_porcupine_safe` approved 2026-11-16).
- kvreconf up to linking (`18296d64f7`): Go `Options.MaxReplicas` (`RandomOptions`: 9), `RandomOptionsN`/`RandomConfigN`/
  `MainN(k)` (k voters, `k + 4` replicas), `TestMainN` (`KVRECONF_MEMBERS`); Lean `OptsOk` over `MaxReplicas`,
  `freshIdsM`, specs and proofs of `RandomOptionsN`, `RandomConfigN`, `MainN` (`1 ≤ k < 2^59`). Every kvreconf and
  kvdurable module but `Link`/`Results`/`Adequacy*` builds (verified 2026-11-16, targets `/shared/tmp/kvraftN/targets.txt`).
  `TestMainN` 20 runs at 18296d64f7: all PASS (k = 1 ×4, 3 ×6, 5 ×4, 7 ×6; 1.5 to 15 s each) (`/shared/tmp/kvraftN/kvreconf-runs20.txt`, logs `run<i>.log`).
- `raft_kvreconfN_porcupine_safe` approved by the user (2026-11-16, via etcd-grove-02; `notes/kvreconfN-draft.md`) and
  linked (`da91401f22`): `kvreconfProgramN`, `kvreconfN_adequate_of`, `raft_kvreconfN_adequate`, `kvreconf_MainN`, the
  closed theorem in `Results.lean` (same 328 axioms as `raft_kvreconf_porcupine_safe`). lean merged again (`a48cf8827d`, at ee15ea8d45 after k8s-7f5),
  bounds +1 accepted (Q8, etcd-grove-02) and recorded (`b1da2fa1a4`). **Landed: lean `5d2a12df97`** (etcd-grove-02 reran `etc/land.sh`; the first
  run's k8s gate failure was two gate runs at once on fixed ports, not this branch).


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
