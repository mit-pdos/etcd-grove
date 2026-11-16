# k8s 7f-6 stage C (the bridge): handoff

## START HERE
- Branch `k8s-7f6c` (worktree `/shared/etcd-grove-k8s7f6c`), based on `k8s-7f5` at `edf33c7a14`.
- Plan and forms: `notes/k8s-7f6c-plan.md` (§1 target, §2 F1's counterexample, §3 lemmas, §4 forms);
  decisions: `questions.md` (untracked).
- Done:
  - F1 (decided by etcd-grove-02, option 1): `KvOne` and `KvNext`'s fourth conjunct
    (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Updates.lean`); producers re-proved: `kvOne_optPut`,
    `kvOne_optDel` (`Steps.lean`), used by `store__Create`, `store__updateOnce`, `store__deleteOnce`;
    `seedOp_one` (driver `Seed.lean`); destructuring fixed in `Inv.lean`, `InvSteps.lean`.
  - The bridge, `Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/KWatchBridge.lean`:
    `streamOkL_of_kStreamOk`, `histWf_of_krel`, `kStreamOk_hist`, `kModeOk_of`; no `sorry`, no axiom.
- Next (stage E): produce `KHistW σ` at the configuration (`comp`: a `KOk` conjunct from the boot state
  and `KvExt`; `wf`: `KOk.hwf` under `CfgD`; `one`: carry `∀ cs ∈ σ.changes, cs.length ≤ 1` from
  `KvNext`'s `KvOne`), `1 ≤ σ0.rev` from E's `Q`, `hlk` from the watch input's `kInOk`.
- Pitfalls: a copied `.lake/build` from the main checkout is against `.lake/packages/perennial`, so the
  first targeted build here rebuilt ~4000 modules (about an hour); seed from a worktree on
  `manifest-e9e.json` instead. `lean-check` lists stale errors after an incremental check: use `-a`.
- Build: `TMPDIR=/shared/tmp systemd-run --scope -q -p MemoryMax=64G lake build
  --packages=/shared/tmp/manifest-e9e.json Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchBridge`;
  the importers of the changed files: `etc/importers.py --leaves` of `Updates.lean`, `Steps.lean`,
  `Seed.lean`, `KWatchBridge.lean`.
