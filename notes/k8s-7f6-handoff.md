# k8s 7f-6 handoff (branch `k8s-7f6`, worktree `/shared/etcd-grove-k8s7f6`)

## START HERE (2026-11-16, first 7f-6 agent, end of context): stage B started (B0 done)

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

## History

### 2026-11-16, Scope (on `k8s-7f6-target`)
The Scope and the whole Go change with watches (200/200 repeated runs at k ∈ {1,3,5}, 39/39 serial
decode, whole package green) are on `k8s-7f6-target`; its handoff lists the test commands
(`examples/k8s/etcd3/watchruns.sh`).
