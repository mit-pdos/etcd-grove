# k8s-unified: handoff

## START HERE

Branch `k8s-unified-scope`, worktree `/shared/etcd-grove-k8sunified` (lean 5a18d777d2 merged; pin
c44b74871: `--packages=/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`;
`.lake/build` seeded from mergeorigin10). Scope: `notes/k8s-unified-scope.md` (decisions §7);
`questions.md` (untracked) has the decisions.

Done:
- U0 (commit "k8s-unified U0"): `examples/k8s/all` (Go `Main`, tests pass), project `k8s-all`
  translated, gen-init root/program (`Proof/.../k8s/all/{Init,InitLinked,PkgTable}.lean`),
  featuregate INSIDE. The idutil docstring change (approved, D5) is deferred to U3's full build
  (it rebuilds the server's cone): `/shared/tmp/k8s-unified/idutil-docstring.patch` (`git apply`).
- U1: `Proof/.../k8s/all/{Base,holdToken,Main,MainLinked,TopLevelDefs}.lean`,
  `Spec/.../k8s/all/{holdToken,Main,TopLevelRobustness}.lean`; `Main.wp_proof` and `k8s_all.wp_Main`
  check (lean-check, 0 errors).

STOP now: the statements below to etcd-grove-03/the user. Next after approval:
1. `Proof/.../k8s/all/Adequacy.lean` (`k8s_adequate`, via `etcd_adequate_alloc_members`: ms =
   `k8s_etcd3N.startAddrs k ++ cluster3.members clusterCfg`, Bs = bridges ++, As = `k8sAddrs k`,
   Ds = `k8sDirs k`; two disjointness lemmas; both `schedLit`s; registry allocated as the compactor's),
   `Results.lean` (`k8s_all_Main`, `k8s_safe`, `#print axioms`), `Proof/.../all/TopLevelRobustness.lean`.
2. U3: retire the five old closed theorems (etcd3/compactor `Adequacy`, `_safe`s, `TopLevelRobustness`
   pairs, `TopLevelDefs`, PROGRAMS entries/PkgTables), apply the idutil patch, tcb collection
   `etc/tcb-collections/k8s-all.txt`, STATUS, full timed build, checks; attack subagent; land stop.

## The statements (for review)

`k8s_robust.spec`: `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/TopLevelRobustness.lean`
(elaborates: build of 2026-11-20). `k8s_safe` (to be written in `Results.lean`, the n-step form, as
the retired `_partition_safe`s): the same binders up to `HEnv`, then `(n : Nat)`, `Hprem₁`/`Hprem₂` at
`n` (no `∀ n`), `σ g Hfs HWal`, `(Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads :
σ.threads = 1) (κs t2 σ2) (Hsteps' : RealNsteps n ([k8sProgram k clients ops watchers wops steps₁
steps₂], ((σ, g) : CfgState)) κs (t2, σ2)) (Hn : n + 2 ≤ 2 ^ 28)`, concluding
`(∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
(∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)`.
