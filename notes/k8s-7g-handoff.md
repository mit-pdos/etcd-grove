# k8s 7g (the maintainers' checker): handoff

## START HERE

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`), off `lean` 9702d5707e. There is no
  `.lake/build`: the Scope stage needed none.
- **State: Scope committed, at its hard stop** (`notes/k8s-7g-scope.md`), for etcd-grove-03 and the user.
  No Lean is edited and no translation regenerated.
- Done:
  - Scope (§1 translation and trust specs, §2 bridge B1-B5, §3 statements, §4 TCB delta, §5 steps
    8.1-14k lines, §6 risks, §7 Q1-Q8);
  - Go experiment (§8);
  - `notes/k8s-7g-experiment.patch` (the driver diff and the tests, against `k8s-7f6`) and
    `notes/k8s-7g-d30g.patch` (the D30g patch to upstream's `model.go`);
  - nonissue `k8s-correctness-watchvalidator-cut-before-bookmark`.
- Next, in order, after the decisions and 7f-6 E+F has landed:
  - step 0 (Go: the copy, the gate, the driver changes, the translation);
  - step 1 (trust specs: hard stop);
  - then steps 2-6 (Scope §5).
- Open decisions: Scope §7 Q1-Q8 (recommended: A', a copy plus a gate, a `NeedsRewrite` field,
  accept D7g-1/2/3, a decimal `SetResourceVersion` only, `Output.Raw`, local `maps` specs plus a
  Perennial proposal).
- Pitfalls:
  - The experiment test's partition runs must read the schedule from `K8S7G_SCHED`: `inChild`
    overwrites `K8SETCD3_SCHED`. One batch ran without schedules because of this.
  - A run needs its own working directory (`t.Chdir(t.TempDir())`): a leftover `k8s7g.etcd` makes
    the seeding fail ("store").
  - `cmp.Diff` and `reflect.DeepEqual` tell nil from empty slices: state the specs with non-nil.

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
