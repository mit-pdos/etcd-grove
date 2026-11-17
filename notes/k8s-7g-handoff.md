# k8s 7g (the maintainers' checker): handoff

## START HERE

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`), off `lean` 9702d5707e. There is no
  `.lake/build`.
- **Scope approved by the user, 2026-11-17, via etcd-grove-03**: design A' and the
  recommendations on Q2-Q8 (`notes/k8s-7g-scope.md` §7; `questions.md`).
- Done:
  - Scope and Go experiment, `ecf71b5f6a`;
  - `notes/k8s-7g-experiment.patch` (the driver diff and the tests) and `notes/k8s-7g-d30g.patch`;
  - nonissue `k8s-correctness-watchvalidator-cut-before-bookmark`.
- **Next: step 0, only after 7f-6 E+F lands** (the coordinator relaunches). First merge `lean`.
  Step 0 is the Go work: the copy, the gate and the driver changes of Scope §1.4, then the
  translation. Then steps 1-6 (Scope §5).
- **Hard stops:** step 1's trust-spec texts (`DeepEqual`, `cmp.Diff`, `maps`/`slices`, …) and
  step 6's Freeze.
- Pitfalls:
  - The experiment's partition test reads its schedule from `K8S7G_SCHED`: `inChild` overwrites
    `K8SETCD3_SCHED`.
  - Each run needs its own working directory: a leftover `k8s7g.etcd` makes the seeding fail.
  - `cmp.Diff` and `reflect.DeepEqual` tell nil from empty slices.

## Re-running the experiment

```
# scratch tree: git archive k8s-7f6 examples third_party | tar -x -C /shared/tmp/k8s7g/src
# then apply notes/k8s-7g-experiment.patch, and copy upstream's types/model/replay/watch/consistency/
# storage.go (module cache, k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038/pkg/storage/testing/
# correctness) into examples/k8s/etcd3/correctness/ with notes/k8s-7g-d30g.patch applied
cd /shared/tmp/k8s7g/src/examples/k8s/etcd3
export PATH=/usr/local/go/bin:$HOME/go/bin:$PATH TMPDIR=/shared/tmp GOWORK=off GOFLAGS=-mod=mod
systemd-run --scope -q -p MemoryMax=32G go test -count=1 -v -run 'TestD30gRealModel|TestDeepEqualFacts|TestValidatorDepartures' . ./correctness
K8S7G_FLOOR=1 systemd-run --scope -q -p MemoryMax=32G go test -count=1 -v -run 'TestRealChecker$' .
/shared/tmp/k8s7g/partruns.sh   # k = 3, six schedules (K8S7G_SCHED), the floor on
```

Switches: `K8S7G_PATCH` (D30g, default 1), `K8S7G_SETRV` (decimal `SetResourceVersion`, default
1), `K8S7G_FLOOR` (the seed floor, default 0), `K8S7G_TRUNC` (cut after the first Error, default
1), `K8S7G_REQUIRE_OK=1` (fail unless the real checker is `Ok`).
