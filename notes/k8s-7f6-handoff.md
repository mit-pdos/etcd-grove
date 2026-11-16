# k8s 7f-6 handoff (branch `k8s-7f6`, worktree `/shared/etcd-grove-k8s7f6`)

## START HERE (2026-11-16, first 7f-6 agent): stage A built, unlinked; HARD STOP for its closed statements

- **Branch:** `k8s-7f6` off lean `ee15ea8d45` (reset there for stage A); the full 7f-6 Go target
  (watch traffic, `WithCancel`, tests, Scope) is on branch **`k8s-7f6-target`** (`4952cb3b91`).
  Decisions: worktree `questions.md` (untracked). Scope: `notes/k8s-7f6-scope.md`.
- **Done (stage A, `k` members, no watches):** Go `startCluster(k)`/`MainCluster(k,…)`/
  `MainPartition(k,…)` (`examples/k8s/etcd3/k8setcd3.go`, tests moved to `startCluster(3)`/`testK`),
  translation regenerated (`etc/goose.py --project k8s-apiserver --perennial /shared/perennial-e9e6351d9`),
  Lean: `ClusterN.lean` (vocabulary, namespace `k8s_etcd3N`), `DirN.lean`, `bridgeAddr`, `holdToken`,
  `startCluster` (spec+proof), `MainCluster`/`MainPartition` (spec+proof) — all build; `Init`/`PkgTable`
  regenerated (`etc/gen-init.py`); `clusterConfig` deleted.
- **Hard stop:** `notes/k8s-7f6a-statements.md` (old → new closed statements, Lean + English). The user
  approves each before linking.
- **Next, after approval:** `Adequacy.lean` (cluster/partition at `k`: txnlinfaultsN's `Adequacy.lean`
  is the model; `k8setcd3CProgram k …`, `k8s_etcd3N.k8setcd3NAddrs/Dirs`, the `etcd_adequate_members`
  facts from `DirN.lean`), delete `Cluster.lean`/`k8setcd3CAddrs`/`k8setcd3CDataDirs`, `MainLinked.lean`,
  `Link.lean` (`etc/gen-link.py`, check how the k8s etcd3 link is generated), `Results.lean`, tcb
  collection (`--check --update` only if it moves), `etc/gen-interface.py` for touched APIs, STATUS,
  full build under the flock, then report for land. Then stage B (Scope §5).
- **When 7f-5's `store__Watch.lean` is on lean:** merge lean (after stage A lands), use
  `k8s.store.Watch.spec`.
- **Pitfalls:**
  - Lean names in namespace `k8s_etcd3` shadow the `k8s_etcd3N` ones (`token`): qualify them.
  - `clientCfgOk`: `iframe #` closes the endpoints slice; what is left is `DialOptions` nil, the pure
    part and `clientAuthPre` (see `startCluster.lean`).
  - Every cluster Go test runs in a child process (fixed ports); never two test binaries at once.
    `K8SETCD3_K` picks `k` (default 3), `K8SETCD3_SCHED` the schedule.
  - `gofmt` is `/usr/local/go/bin/gofmt`.
- **Build:** `--packages=/shared/tmp/manifest-e9e.json` everywhere (lean-check: `LAKE_OPTS=...`);
  targeted builds under `systemd-run --scope -q -p MemoryMax=64G`; `.lake/build` seeded from
  `/shared/etcd-grove-k8s7f` (2026-11-16). Gates: `flock /shared/tmp/etcd-grove-full-build.lock`.

## History

### 2026-11-16, Scope (on `k8s-7f6-target`)
The Scope and the whole Go change with watches (200/200 repeated runs at k ∈ {1,3,5}, 39/39 serial
decode, whole package green) are on `k8s-7f6-target`; its handoff lists the test commands
(`examples/k8s/etcd3/watchruns.sh`).
