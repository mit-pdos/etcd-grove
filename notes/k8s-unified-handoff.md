# k8s-unified: handoff

## START HERE

Branch `k8s-unified-scope`, worktree `/shared/etcd-grove-k8sunified` (lean 5a18d777d2 merged; pin
c44b74871: `--packages=/shared/tmp/manifest-c44.json`, `PERENNIAL_DIR=/shared/perennial-c44b74871`).
Scope: `notes/k8s-unified-scope.md` (decisions §7); `questions.md` (untracked) has the decisions.

Done (U0-U3; statements approved by the user 2026-11-20):
- U0/U1: `examples/k8s/all`, its translation and initializers, `Main`'s triple (`k8s_all.wp_Main`).
- U2: `Proof/.../k8s/all/Disjoint.lean` (the two clusters' addresses and directories disjoint),
  `Adequacy.lean` (`k8s_adequate`, `wp_schedLit`), `Results.lean` (`k8s_all_Main`, `k8s_safe`),
  `TopLevelRobustness.lean` (`k8s_robust`).
- U3: retired `k8s_etcd3{,_cluster,_partition}_{safe,adequate}`, `k8s_etcd3{,_cluster,_partition}_robust`,
  `k8s_compactor{,_partition}_{safe,adequate,robust}`: deleted both drivers' `Adequacy`, `TopLevelDefs`,
  `TopLevelRobustness` (Proof and Spec) and `PkgTable` (gen-init PROGRAMS entries), the `_safe`
  sections of their `Results.lean` (triples kept), collections `k8setcd3.txt`/`k8scompactor.txt`;
  new `etc/tcb-collections/k8s-all.txt` (597 axioms = their union); idutil docstring patch applied;
  README, STATUS (entry; history append-only), leasecatchup comments.
- Checked: full timed build `20261120-145821-645806`; tcb --check (674 axioms, 2 sorries, unchanged);
  69 collections; gen-link modes; interfaces --check --layout; api; tier; gen-init; featuregate;
  mode; bounds; goose; axiom-tok; `examples/k8s/all` Go tests. Independent attack on the idutil
  docstring and `Hlow`: both survive (no restarts in this program; one generator per member).

STOP: the land stop (report to etcd-grove-03; do not commit after it). If lean moves before the
land: merge it, seed `.lake/build` as common-rules say, rebuild, rerun the checks.

## The statements (for review)

`k8s_robust.spec`: `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/TopLevelRobustness.lean`
(elaborates: build of 2026-11-20). `k8s_safe` (to be written in `Results.lean`, the n-step form, as
the retired `_partition_safe`s): the same binders up to `HEnv`, then `(n : Nat)`, `Hprem₁`/`Hprem₂` at
`n` (no `∀ n`), `σ g Hfs HWal`, `(Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads :
σ.threads = 1) (κs t2 σ2) (Hsteps' : RealNsteps n ([k8sProgram k clients ops watchers wops steps₁
steps₂], ((σ, g) : CfgState)) κs (t2, σ2)) (Hn : n + 2 ≤ 2 ^ 28)`, concluding
`(∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
(∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)`.
