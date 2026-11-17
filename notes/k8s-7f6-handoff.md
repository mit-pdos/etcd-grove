# k8s 7f-6 handoff (branch `k8s-7f6`, worktree `/shared/etcd-grove-k8s7f6`)

## START HERE (2026-11-17, seventh 7f-6 agent): stage E, past checkpoint E-1 (approved)

- **Branch:** `k8s-7f6`. Go target `k8s-7f6-target` `c6bfeb69e8`. Plan `notes/k8s-7f6e-plan.md`;
  decisions in worktree `questions.md` (E-1 APPROVED by etcd-grove-03).
- **Done, built:** §8(ii) `startCluster` with `kvWatch_served`, `clusterUp` gains `ws γrc m0`, the
  members' `watchRegAt` at the bridges + read views, `memberOf`, `V = watchEnvL m0 (wmemsOf svs ws)
  γrc wpfx` (b27d8d93db). `startCluster.wp_proof` takes the two mvcc laws (`Hp Hr`): link them.
- **Done, built (this commit):** step 1 (`PendSpec.isObs/obsOk` with defaults, `PStep.obs`,
  `pSeq_obs`; `kSpec` in `KWatch.lean` with the watch observation; `ioOk`; `stepL_sound/complete`;
  `Bounded` + `rv ≤ hist.length`; `Model.spec` premise on `g0`); step 2 (`GenInW`, `GenInA`, `kInOk`;
  `isCache` with `wobjs`, read-only fields, `done` invariant; `getW/putW`, `newWCache`;
  `genWatchFrom`/`genWatch`; `Gen.wp_proof`); step 3 (`KNames.ch/b0`, `revOwn` with the mono list +
  `KHistI`); step 4 (`WatchQ.lean`); step 5 pieces (`kOk_obs`, `watchOkL_errs`, `kWEvRel` +
  `zObj`, `watch_commit`, `WatchCommit.lean`); `Apply.spec` gains `γk`, `kInv γ c g0 γk`,
  `storeWatchOk sp c driverW γk`, `watchListOn`; `kOk_ok/errR`, `read_err_commit` take `Kind ≠ 5`.
- **Done, built (cf15db4386):** step 5 `Apply.wp_proof` (watch branch: `runWatch` at `watchQ`, the
  commit `watch_commit` with `watchOkL_errs`/`watchOkL_stream_commit`, `putW`; `done.Add(1)` on the
  unary paths, macro `done_add`); step 6 `Check` over `RunLin2` (spec: `γk`, `watchers wops`, their
  bounds, `kInv γk`, `storeWatchOk`, `watchListOn`, Model's rv premise); `encodeWEvents`/`runWatch`
  posts carry the encodings' lengths (WEvOk); `GenInW`: skipped ⇒ `MinRV = []`.
- **Done, built:** `runtime.Decode.spec`/proof (`Spec|Proof/k8s_io/apimachinery/pkg/runtime/Decode.lean`,
  generic over the decoder's method), `codec.Decode.spec`/proof (the driver's, `codec__Decode.lean`).
- **Done, built (step 7(v)):** `storage.AnnotateInitialEventsEndBookmark` spec/proof (generic over the
  object's `GetAnnotations`/`SetAnnotations` contract), `Obj.GetAnnotations`/`Obj.SetAnnotations`
  specs/proofs, `newObj.spec` post `objAtD x dzero []` (Main*'s `%o %ho` uses break until step 8),
  `WContract.lean`: `watchContractOk_driver` (`isPkgInit driver ⊢ watchContractOk driverSpec driverW
  codecI`) and `newItemOk_driver` (`newItemOk driverSpec (functions newObj [])`).
- **Done, built (step 7(iii)-(iv)):** `WatchEnvN.lean`: `clientWatchOk_of_regs` (clusterUp's
  registrations + `isNewClient` + `kvReadAu γk OneChange` (`one_read_au`) ⇒ `k8s.clientWatchOk cl γk`;
  for `k` bridges and Main's one address), via `memberWatch_of_reg`, `streams_of_regs`.
- **Done, built (step 8):** `newStore.spec`/proof (seed, features, `etcd3.New`; post: seed cell at
  `σs2`, `isStore sp (storeCfgD …)`, `□ ∀ γk, clientWatchOk cl γk -∗ storeWatchOk sp (storeCfgD …)
  driverW γk`); `storeCfgD` in `WContract.lean`.
- **Next, in order:** step 9 `Main*` (single member: `kvWatch_served` at `clientAddr`). **E-2 hard stop**
  before linking (Link/MainLinked/Adequacy/Results): report old → new closed texts.
- **Pitfalls:** build slots are often both busy (a full c6b build retries): queue builds in the
  background and write ahead; lean-check spins at "elaborating line 1" until the imports are built
  by `lake` (then it works, ~1 min per file). `subst` on `g' = g` eliminates `g`: `subst g'`.
  `simp` normalizes `W64 5` to `5#64`: use `decide_eq_true h`/`decide_eq_false h`. `wp_join`:
  bind without `as`, solve cases with `jcases` (genWatchFrom.lean: solves the goals it can fully, the
  continuation is a wand and is skipped), then `iintro`; a case at its join value is `True ∗ R`
  (`jfin`); `wp_auto` drops dead locals (don't pass them to a later join); persist read-only locals.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build T...`;
  lean-check `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json`, `--max-open 2`.

## History

### 2026-11-17, sixth 7f-6 agent: stage E, at checkpoint E-1

- **Branch:** `k8s-7f6`. Go target `k8s-7f6-target` `c6bfeb69e8` (kept in step). Plan:
  `notes/k8s-7f6e-plan.md` (GO by etcd-grove-03, decisions in `questions.md`); E-1 = its §8.
- **Done:** Go with watchers + G1/G2, translation, Init/PkgTable (b99bfd3fc8; tests pass, watchruns
  26/26). `etcdstart.kvWatch_served`/`watchRegAt` (`lib/etcdstart/WatchServed.lean`) and
  `etcdstart.watchEnvL`/`watchEnvL_conn` (`lib/etcdstart/WatchEnvL.lean`): both build (b785daaae7).
- **Broken on purpose until E is done:** the k8s etcd3 proofs of `Gen`, `newCache`, `Apply`,
  `Check`, `Main*` (the Go moved); nothing else.
- **Next, in order:** after E-1's review, plan §8 (ii): `startCluster`'s Serve step with
  `kvWatch_served`, `clusterUp` gains the members' registrations (shape in §8); `Main` the same; then
  plan §3 steps 1-6, 7(iii)/(v), 8-10. Checkpoint E-2 (closed statements) is a hard stop.
- **Pitfalls:** lean-check sat at "elaborating line 1" for minutes on the new files: `lake build` the
  module through the build slot instead (20-30 s each). `ihave #` on `srvWOk` needs `haveI :=
  v3rpc.srvWOk_persistent Hp …` first. `List.Nodup.getElem_inj` (not `_iff`). The Go target and this
  branch change together (copy `watch.go`/`k8setcd3.go` there and commit).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build T...`;
  Go tests: `cd examples/k8s/etcd3; GOWORK=off go test -run ...` under `systemd-run --scope -q -p
  MemoryMax=32G`; `watchruns.sh` with `BIN`/`OUT` under `/shared/tmp/k8s7f6e`.

### 2026-11-17, sixth 7f-6 agent: stage E planned (fbe30a9a73)

- **Branch:** `k8s-7f6` at lean `1612a1143a` (stage D landed) + this plan commit. Go target
  `k8s-7f6-target` `88a1646324` (worktree `/shared/tmp/k8s7f6d/target`). Decisions: worktree
  `questions.md` (untracked).
- **Done:** the stage E plan, `notes/k8s-7f6e-plan.md` (E with F: model observation, inputs, the
  invariant's mono list and `KHistW`, the watch's `Q`, `Apply`'s commit, `Check`, the `k`-member watch
  environment, `newStore`, `Main*`, link). No Lean or Go edited.
- **Next, after the coordinator's go:** the plan's §2 Go (G1 clamp, G2 `wobjs`; port the target's
  `k8setcd3.go`), then §3 steps 1-10 in order; checkpoints E-1 (watch registration shape) and E-2
  (closed statements, hard stop before linking), then the land stop.
- **Open (plan §6):** G1/G2; E+F one land; generic `PendSpec` observation; the watch environment in
  7f-6 (revised estimate 3400-4600 lines); drop `done ≤ total`.
- **Pitfalls:** see the fifth agent's below (lean-check spinning at line 1 = an import that does not
  build; `wp_if_destruct`/`wp_apply` already run `wp_auto`; Go constants need `simp only`).
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build T...`;
  lean-check `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json`, `--max-open 2`; gates under
  `flock /shared/tmp/etcd-grove-full-build.lock`.

### 2026-11-16, fifth 7f-6 agent: stage D done (landed, lean 1612a1143a)

- **Branch:** `k8s-7f6` (lean `3a0a47deb1` merged, `a7c843fab8`). Go target `k8s-7f6-target`
  `88a1646324`. Decisions: worktree `questions.md` (untracked; annAt and D forms ACCEPTED).
- **Done (D):** Go + translation (dfc8fc428d); annAt (f969619c10); `WRun.lean`, `watchOptions`,
  `toWEvent`, `encodeWEvents`, `lastObj` (1702ae42de, c651ec6b1f, 6b2fe2f294); `consume.wp_proof`
  (8981aeebbf); `watchEvents`/`runWatch` specs and proofs over `store.Watch.spec`, and the whole watch
  run linked in the driver's `Link` (`etc/link-lean-first-k8setcd3.txt`, 5cef7d43b5). Nothing linked
  calls `runWatch` yet: no closed statement moved.
- **Specs (internal, forms):** `watchEvents.spec`: store.Watch's premises with `opts := watchOptsV x p`
  (key, parsed `MinRV`), pre `isStore`, `storeWatchOk sp c driverW γk`, feature gates, `Q`'s updates;
  post `failed → sieOfL x = some false ∧ n = 0`, else `wevsOwnM sl wes`, `Forall₂ kWEvRel kes wes`,
  `kSeen c (selD x) (predEmptyL x) (kScopeOf c k x.Recursive') (kModeOf (sieOfL x) x.Bookmarks' n) Q kes`.
  `runWatch.spec`: the same premises only for `x.Skip' = false`; post `wFailedOut` (skipped or failed)
  or `wEventsOut (encWEventsL wes)` with `lastObjL wes`.
- **Next:** the coordinator's go for etc/land.sh (no commits while it lands); then stage E (Scope §5:
  the wiring, `Apply`'s `KWatch` branch over `runWatch.spec`) and the stage E obligations (History).
- **Pitfalls:** lean-check "elaborating line 1" forever = an import that does not build (here: a new
  Spec file with an error, `isStore` must be `k8s.isStore`). `lake build` the new imports first and
  read its errors; then lean-check works (consume.lean: ~1 min fresh, then seconds per edit).
  `wp_if_destruct`/`wp_apply` already run `wp_auto` (a following `wp_auto` fails "no progress");
  `wp_apply (lc := 2) f` gives `Hlc1 Hlc2` for a select; Go constants (`hiccupDuration`) need
  `simp only [<pkg>.hiccupDuration]` before `wp_auto` sees them; a `wp_join` over a branch that
  `return`s needs `(Q := fun v => (⌜v = executeVal⌝ ∗ …) ∨ (⌜v = returnVal #()⌝ ∗ …))`; spatial
  hypotheses the case needs (`timer`) go in its `with [...]`; reduce `if ok = true` with
  `rw [ite_eq_left rfl]`/`rw [ite_eq_right Bool.false_ne_true]`.
- **Build:** `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build T...`;
  lean-check `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json`, `--max-open 2`; gates under
  `flock /shared/tmp/etcd-grove-full-build.lock`.

### 2026-11-16, fourth 7f-6 agent: D's Go, annAt, WRun, the leaves, consume.spec

- Stopped at consume.wp_proof (done by the fifth agent); see the commits above.

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
