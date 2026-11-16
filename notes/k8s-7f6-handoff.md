# k8s 7f-6 handoff (branch `k8s-7f6`, worktree `/shared/etcd-grove-k8s7f6`)

## START HERE (2026-11-16, fourth 7f-6 agent): stage D started, STOPPED on a spec defect

- **Branch:** `k8s-7f6` (lean `8448906500` + this checkpoint). Go target `k8s-7f6-target` now `88a1646324`
  (watch.go = lean's B1 split + D's functions; its watch tests pass, 83.7 s). Its scratch worktree:
  `/shared/tmp/k8s7f6d/target`.
- **Done (this checkpoint):** D's Go (`runWatch`, `watchEvents`, `consume`, the timing constants) on
  `k8s-7f6`'s watch.go with its translation (`etc/goose.py --project k8s-apiserver`; `gen-init --check`
  clean; Code/GeneratedProof modules build). No Lean spec or proof of D yet.
- **Risks checked:** context producers exist (`wp_WithCancel_Background_of` gives `ctxValueFrom`;
  `metadata.outgoingCtxOkC_bgFrom`, `k8sctx.k8sCtxOk_bgFrom`; `ctxErrClient` from `ContextErrsClient`);
  Perennial's `time` specs (`NewTimer`/`isTimer` a chan bag, `After`, `Timer.Stop`, `Sleep`, `Since`, `Now`)
  exist; an SPSC receive in a `select` is `spsc_rcv_au`'s `recvAu` (precedent `watchChan__serialProcessEvents`).
- **BLOCKER (ledger 2026-11-16, "the watch's annotated object is not expressible for the driver"):**
  no `W : WatchSpec DObj` satisfies `watchContractOk driverSpec W codec` (`objAtD` pins `Annotated' = false`,
  Go's annotate sets it), so `storeWatchOk` is unobtainable for the driver and `toWEvent` cannot give
  `kWEvRel` for the annotated bookmark. Proposed: `WatchSpec.annAt` (ownership predicate) in place of
  `annotate`. Waiting for etcd-grove-02's decision.
- **Next, after the decision:** (if accepted) the WatchDefs/transform/New change (whoever the coordinator
  names), then D in order: `watchOptions`, `toWEvent`, `encodeWEvents`, `lastObj`, `consume`, `watchEvents`,
  `runWatch` (Scope §5; post: `WFailed`, or the encoded events `ws` with `Forall₂ kWEvRel kes ws` and either
  `kNonErr kes = []` or `□ Q lb σ ∗ □ Q lb0 σ0 ∗ ⌜kStartOk m σ0 st ∧ kStreamOk … σ st kes⌝`: what
  `streamOkL_of_kStreamOk` takes). Done token: `PDone' := dghostVar γd discard true`, driver holds the
  full `false`, updates it after `Stop`, then `cancel`.
- **Stage E obligations from B:** still open (History, third agent).
- **Pitfalls:** as in B (below); `etc/goose.py` with GOWORK unset; the Code change rebuilds every importer.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build T...`;
  lean-check `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json`, `--max-open 2`; gates under
  `flock /shared/tmp/etcd-grove-full-build.lock`.

## History

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
