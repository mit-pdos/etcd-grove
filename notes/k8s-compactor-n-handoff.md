# k8s-compactor-n: handoff

## START HERE (2026-11-20)

- Branch `k8s-compactor-n`, worktree `/shared/etcd-grove-compactorn` (off lean `d45f8b140e`; `.lake/build`
  seeded from `/shared/etcd-grove-bprime`, built at that lean). Pin c44b74871: `--packages=/shared/tmp/manifest-c44.json`,
  `PERENNIAL_DIR=/shared/perennial-c44b74871`.
- State: plan written (`notes/k8s-compactor-n-plan.md`), reported to etcd-grove-03; **stopped for the
  user's approval of the new `k8s_robust.spec` (§4) and the bound `k₂ ≤ 600` (§3)**. No Lean or Go edited.
- Next after approval: §1 Go change + tests, `etc/goose.py`, then §2 in table order.
- Id search scripts: `/shared/tmp/compactorn/{ids,first}.py`.
