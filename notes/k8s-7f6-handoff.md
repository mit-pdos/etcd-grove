# k8s 7f-6 handoff (branch `k8s-7f6`, worktree `/shared/etcd-grove-k8s7f6`)

## START HERE (2026-11-16, fourth 7f-6 agent): stage D in progress (consume next)

- **Branch:** `k8s-7f6` (lean `8448906500` + D commits). Go target `k8s-7f6-target` `88a1646324`
  (lean's B1 split + D's Go; watch tests pass). Scratch worktree of it: `/shared/tmp/k8s7f6d/target`.
- **Done:** D's Go + translation (dfc8fc428d); the annAt change (f969619c10, ledger 2026-11-16 "the
  watch's annotated object...", decided by etcd-grove-02): `WatchSpec GF Obj` with `annAt`, every
  binder `WatchSpec GF Obj`, 7f-5's proofs unchanged, etcd3 store `Results` builds (no etcd3 API list,
  so no interface files); `WRun.lean` (`driverW`, `watchOptsV`, `predOk_driverW`, `lastObjL`,
  `dobj_countable`, `doneTok`/`donePD`, `kCancelled_refute`, `kSeen`, `kStopOk`,
  `monoList_idxs_agree`); proved: `watchOptions` (returns the cell owned, `sendInitOwn`: persist it in
  `watchEvents`), `toWEvent` (`kWEvRel`), `encodeWEvents` (`encWEventsL`, no premise), `lastObj`;
  `consume.spec` and the select helpers `wp_select_bag_bag`/`wp_select_bag_spsc` (`consume.lean`).
- **Next, in order:** `consume.wp_proof` (callees: `toWEvent`, `time.NewTimer`/`After`/`Timer.Stop`;
  loop invariant: received `recv`, `kes`, `wes`, slice `sl ↦* ws` + cap, `Forall₂ kWEvRel`,
  `[∗list] idx γ.evs kes`, `kSeen kes`, `spscConsumer γ.res recv`, `kLive`, `doneTok`; per element:
  `monoList_idxs_agree` makes the element's prefix `kes`, `kCancelled_refute` drops its cancellation
  branch); then `watchEvents` (WithCancel(Background()) with `PDone' := donePD γd`, `doneTok` from
  `dghostVar_alloc`, `outgoingCtxOkC_bgFrom`/`k8sCtxOk_bgFrom`/`ctxErrClient`, `store.Watch.spec`,
  consume, Stop with `kLive`, `dghostVar_persist` the token, cancel), `runWatch`; link list; land stop.
- **Stage E obligations from B:** still open (History, third agent).
- **Pitfalls:** lean-check stalls at "elaborating line 1" on `consume.lean` even with its imports built
  (twice, ~10 min each; `lake build` of the file takes ~1 min): iterate with lake builds there.
  `wp_start as H` (not a ⟨Hpkg, H⟩ pattern: wp_start extracts isPkgInit); `iunfold X at H` for
  hypotheses; a returned fresh cell cannot be persisted at `Φ` (no update there): return it owned.
  `wp_if_destruct` on `#!decide P` gives the `P` branch first.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build T...`;
  lean-check `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json`, `--max-open 2`; gates under
  `flock /shared/tmp/etcd-grove-full-build.lock`.

## History

### 2026-11-16, fourth 7f-6 agent: stage D started, stopped on the annotation defect (resolved)

- D's Go and translation; the defect (no `W : WatchSpec DObj` satisfies `watchContractOk driverSpec`)
  recorded and accepted as `annAt`.

### 2026-11-16, third 7f-6 agent: stage B done (landed)

- **Branch:** `k8s-7f6` (lean `d559d8bc9f` merged). Go target: `k8s-7f6-target` (`4952cb3b91`): its
  watch.go predates the B1 split: **port the B1 split (and B2's `step`) there before stage D.**
  Decisions: worktree `questions.md` ("Stage B1 decisions", "Stage B2: forms").
- **Done:** B0 (pure watch.go, `KWatch = 5`); B1 (062592fb62: spec+proof of every check function,
  `WDefs`); B2 (d99e51907d): Go `step`'s `KWatch` branch first (`watchOk`), translation; `stepL` gains
  `if x.Kind' = W64 5 then (if watchOkL x y g.st then [g] else [])`; `step.spec` premise
  `x.Kind' = W64 5 → rv < 2^63 ∧ parsed MinRV < 2^63`; `step.wp_proof` over `watchOk.spec`;
  `stepL_sound`/`stepL_complete`/`step_closure_ok`/`step_result` take `x.Kind' ≠ W64 5`, from
  `k8setcd3S`'s `ioOk` (now `∃ x y, … ∧ x.Kind' ≠ W64 5`), discharged in `Apply.lean` from `GenIn`;
  all B1 functions linked (`etc/link-lean-first-k8setcd3.txt`). No closed statement moved.
- **Next:** the coordinator's go, then `etc/land.sh` (`LAKE_PACKAGES=/shared/tmp/manifest-e9e.json
  PERENNIAL_CHECKOUT=/shared/perennial-e9e6351d9`, GOWORK unset). No commits while it lands.
  Then stage D (Scope §5): `consume`, `watchEvents`, `runWatch` over `store.Watch.spec`; deferred from
  B to D/E: `genWatch`/`genWatchFrom`, `watchOptions`, `toWEvent`, `encodeWEvents`, `lastObj`.
- **Stage E obligations (from B):** (a) `ioOk`'s `x.Kind' ≠ W64 5` goes: `kSpec` must give watches
  their meaning (a watch keeps the configuration iff `watchOkL`), then `stepL_sound`/`_complete` drop
  the premise; (b) discharge `step.spec`'s watch premises (store revision < 2^63: `HistWf`; parsed
  MinRV < 2^63: `WatchInOk` of `Gen`'s draws) where watches reach `Step`.
- **Pitfalls:**
  - A missing import `.olean` makes a lean-check worker spin at "elaborating line 1": build the
    imports with `lake build` first and read its errors.
  - Every proof file of the package lands in `Link.lean`'s one environment: a lemma name used in two
    proof files clashes only there (B2: `item_eq_iff` of `changeAt` vs `storeEqual`, renamed
    `item_eq_iff3`; WDefs' `bmStepL_none_foldl` was KWatchStream's, now imported).
  - `go.min`: `FuncUnfold.func_unfold` then `simp only`; `wp_if_destruct` cannot split a projection
    (`cases h : ch.hasCur'` first); a returned fresh slice: persist it in the caller.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build T...`;
  lean-check `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json`, `--max-open 2`, stopped before
  builds; gates under `flock /shared/tmp/etcd-grove-full-build.lock`. Go: `cd examples/k8s/etcd3;
  GOWORK=off go test -run 'TestWatchOkEdges|TestGenWatchCases' .`; translation:
  `PATH=/usr/local/go/bin:$PATH etc/goose.py --project k8s-apiserver` (GOWORK unset).

### 2026-11-16, second 7f-6 agent: B1

- **Branch:** `k8s-7f6` past lean `54c7fb38f0`. Go target: `k8s-7f6-target` (`4952cb3b91`; its watch.go
  predates the B1 split below: port the split there before D). Decisions: worktree `questions.md`.
- **Done (B1, complete):** `WDefs` (`wevOf`, `wevsOwn`/`wevsOwnM`, `chgOf`, `reliableLoL`,
  `watchListOkL`, `keptL`, `rejectsL`, `dec_true`/`dec_false`, `cfgOwn_rv`); spec+proof of every
  check function: `eventsEqual`, `bookmarksOk`, `changeAt`, `toEvent`, `initialEvents`, `evRange`,
  `reliableLo`, `wantEvents`, `nonBookmarks`, `reliableOk`, `initialPrefixOk`, `firstBookmark`,
  `checkedEvents`, `watchListOk`, `watchOk`, `decodeWEvents` (062592fb62). Go: `reliableOk`/`watchOk`
  split into those helpers (79d056c186), `decodeWEvents` overflow-free length check; translations
  regenerated. Linked with B2's `step`.

### 2026-11-16, first 7f-6 agent: B0

- **Branch:** `k8s-7f6` past lean `54c7fb38f0` (stage A landed there). Watch Go target: branch
  `k8s-7f6-target` (`4952cb3b91`). Decisions: worktree `questions.md` (untracked). Scope §5.
- **Done (B0, this commit):** `examples/k8s/etcd3/watch.go` = the target's pure part (generator
  `genWatch`/`genWatchFrom`, `watchOptions`, `toWEvent`, `encodeWEvents`/`decodeWEvents`, `lastObj`,
  `changeAt`, `toEvent`, `initialEvents`, `eventsEqual`, `bookmarksOk`, `watchOk`, `initialPrefixOk`,
  `reliableOk`; `runWatch`/`watchEvents`/`consume` and the timing constants left for stage D);
  `KWatch = 5`; `watch_test.go` (`TestWatchOkEdges`, `TestGenWatchCases`: pass); translation and
  `Init`/`PkgTable` regenerated; k8s etcd3 `Results` builds. `step` is NOT yet changed (so the branch
  builds): its `KWatch` branch is B2.
- **Next, in order:**
  1. **B1, the leaves** (Spec/Proof file each, `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/`),
     each equal to its `KWatch.lean` function: `decodeWEvents` (`decWEventsL`; over `parseRV`,
     `decodeObj`), `eventsEqual` (`evsEqL`), `bookmarksOk` (`bookmarksOkL`), `changeAt`
     (`changeAtL`), `toEvent` (`toEventL`; `predicate` + `mlistMatches.spec` in `PredOk.lean`, as
     `mlist`), `initialEvents` (`initialEventsL`; `keyInScope`, `storeKey`), `reliableOk`
     (`reliableOkL`; `histAt`), `initialPrefixOk` (`initialPrefixOkL`), `watchOk` (`watchOkL x y
     g.st` over `cfgOwn`). Restructure the Go loops if it makes the proof direct, keeping
     `TestWatchOkEdges` green; any Go change must keep it equal to `KWatch.lean`.
  2. **B2:** Go `step`'s branch (on the target branch: `if in.Kind == KWatch { if !watchOk(...)
     {return nil}; return []mcfg{c} }`, first), `stepL` (`KSteps.lean:47`) gains `if x.Kind' = W64 5
     then (if watchOkL x y g.st then [g] else [])`, `step.wp_proof`, and every lemma that unfolds
     `stepL` for `kInOk` inputs (`Kind ≤ 4`).
  3. `genWatch`, `watchOptions`, `toWEvent`, `encodeWEvents`, `lastObj`: with D/E (their callers).
  Then stage B's land stop: full build, gates under `flock /shared/tmp/etcd-grove-full-build.lock`.
- **Parallel lines:** stage C (branch `k8s-7f6c`: `KWatchBridge.lean`, `KvOne` in `KvNext`,
  `Updates.lean`) and 7f-5b (branch `k8s-7f5`: `kvWritesDec` read law in `store.Watch.spec`, which
  7f-6 produces at stage E). Merge lean before landing.

### Stage A (landed: lean 54c7fb38f0, 2026-11-16)

- **Branch:** `k8s-7f6` (stage A, `k` members, no watches), lean merged; the full 7f-6 Go target
  (watches, `WithCancel`, Scope's tests) is on branch **`k8s-7f6-target`** (`4952cb3b91`).
  Decisions: worktree `questions.md` (untracked). Scope: `notes/k8s-7f6-scope.md`.
- **Done:** stage A statements approved by the user (2026-11-16; `notes/k8s-7f6a-statements.md`).
  Go `startCluster(k)`, `MainCluster(k,…)`, `MainPartition(k,…)`; translation; Lean `ClusterN`,
  `DirN`, `bridgeAddr`, `holdToken`, `startCluster` (instance-bound form, bounds baseline unchanged),
  `MainCluster`/`MainPartition`, `MainLinked`, `Adequacy`, `Results` at `k`; `Cluster.lean`,
  `clusterConfig` deleted; `etc/tcb-collections/k8setcd3.txt`: 16 axioms gone (the 3-member start's
  lease/watch registrations), none added; trust base unchanged (870, 4); STATUS entry.
- **Next:** the coordinator's go, then `etc/land.sh` (`LAKE_PACKAGES=/shared/tmp/manifest-e9e.json
  PERENNIAL_CHECKOUT=/shared/perennial-e9e6351d9`, GOWORK unset). Then stage B (Scope §5): rebase
  the watch Go from `k8s-7f6-target` onto the landed stage A; `k8s.store.Watch.spec` is on lean
  (`Spec/k8s_io/apiserver/pkg/storage/etcd3/store__Watch.lean`).
- **Pitfalls:**
  - Lean names in namespace `k8s_etcd3` shadow the `k8s_etcd3N` ones (`token`): qualify them.
  - `clientCfgOk`: `iframe #` closes the endpoints slice; what is left is `DialOptions` nil, the pure
    part and `clientAuthPre` (see `startCluster.lean`).
  - bounds-check counts `threadBound`/`receiptBound` premises in specs, not `ThreadBoundLe` binders.
  - Every cluster Go test runs in a child process (fixed ports); never two test binaries at once.
    `K8SETCD3_K` picks `k` (default 3), `K8SETCD3_SCHED` the schedule. `gofmt`: `/usr/local/go/bin/gofmt`.
- **Build:** `--packages=/shared/tmp/manifest-e9e.json` everywhere (lean-check: `LAKE_OPTS=...`);
  full builds under `flock /shared/tmp/etcd-grove-build.lock`, gates under
  `flock /shared/tmp/etcd-grove-full-build.lock` (both `systemd-run --scope -q -p MemoryMax=64G`).

### 2026-11-16, Scope (on `k8s-7f6-target`)
The Scope and the whole Go change with watches (200/200 repeated runs at k ∈ {1,3,5}, 39/39 serial
decode, whole package green) are on `k8s-7f6-target`; its handoff lists the test commands
(`examples/k8s/etcd3/watchruns.sh`).
