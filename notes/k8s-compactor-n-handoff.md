# k8s-compactor-n: handoff

## START HERE (2026-11-20)

- Branch `k8s-compactor-n`, worktree `/shared/etcd-grove-compactorn` (off lean `d45f8b140e`). Pin c44b74871:
  `--packages=/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`.
- Plan `notes/k8s-compactor-n-plan.md` approved by the user 2026-11-20 via etcd-grove-03 (`k₁ ≤ 1000`,
  `k₂ ≤ 600`, token `k8scompactorN-235946`, the new `k8s_robust.spec`).
- Done: Go (`examples/k8s/compactor`: `startCluster`/`bridgeAddr`/`holdToken`, `MainPartition(k, sched)`;
  `examples/k8s/all`: `Main(k1, …, sched1, k2, sched2)`; `TestMemberIDs` over 1000 + 600 ids, fails at 630
  as the Python search predicted); goose; `etcdstart.StartMembers.spec` takes the compaction mode `cmp`
  (`memberPre … x cmp`, default `false`); etcd3's start lemmas moved to `k8s/etcd3/StartLemmas.lean`
  (defs); compactor `ClusterN`/`DirN`/`startCluster`/`MainPartition` at `k` (`epOfs_alloc` in `NoDup.lean`);
  `Cluster.lean`, `clusterConfig` deleted; `k8s/all` (`Main`, `Disjoint`, `TopLevelDefs`, `Adequacy`,
  `Results`, `TopLevelRobustness`) over `k₁ k₂`.
- State: at the land stop (last section).

## Forms decided

- `clusterUp`'s bridges' slice and address slice are owned (`↦*`), persisted by `MainPartition` (the
  return leaves no update to persist them in `startCluster`).
- The example's KV names are the first member's (`sv0.γr.kv`), `etcdKV` moved by `etcdKV_congr`.
- Internal specs (`startCluster`, `MainPartition`, `k8s_all.Main`, `k8s_adequate`) take `k₂ ≤ 1000`; only
  `k8s_safe`/`k8s_robust` state `k₂ ≤ 600` (`Hlow`'s range).
- `k8s_compactorN.k8scompactorNAddrs`/`k8scompactorNDirs` (the plan's `addrs`/`dirs`).
- The compactor's `startCluster` is listed in `etc/tier-linking.txt` (over `kvWatch_served`, as etcd3's).

## State at the land stop (2026-11-20)

- Full timed build `20261120-175709-1173324` green (lean `d45f8b140e`, not moved since).
- `tcb-report --check`: baseline matches (673 axioms, 2 sorries); collections: only `k8s-all` changed,
  7 axioms gone (`--check --update`: `EtcdServer.leaseTimeToLive.wp_proof` and six `pbLease*T_reg`, reached
  only through `cluster3.StartMember`).
- Gates passed: every gen-link mode, gen-init, gen-k8s-deep, goose --check, gen-raft-tla, copy-part, tier
  (227), api, import-all, interfaces --check --layout (etcdstart regenerated), axiom-tok, errorf-wrap,
  featuregate, mode (456), bounds (399), reader-slot (173), k8s-correctness, joint-landing, issues.
- Go: `examples/k8s/all` (TestMemberIDs, TestAddrs, TestMain) and `examples/k8s/compactor` (all) pass.
- Next: etcd-grove-03 runs `etc/land.sh`. Nothing pushed.
