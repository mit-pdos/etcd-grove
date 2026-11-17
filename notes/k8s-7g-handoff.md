# k8s 7g (the maintainers' checker): handoff

## START HERE

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`); lean 3cd4b72599 (7f-6 E+F) merged
  (`d41993afa5`). `.lake/build` moved from k8s-7f6 (built at lean). Pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json`; `.lake/package-overrides.json` is that manifest.
- Scope approved by the user 2026-11-17 (design A', Q2-Q8): `notes/k8s-7g-scope.md`.
- Done: **step 0 (Go)**, `e9bf69f83a`: the copy `examples/k8s/etcd3/correctness/` + gate
  `etc/k8s-correctness-check.py` (gates.sh, CI) + `etc/k8s-correctness/d30g.patch` (moved from
  notes/); the driver changes of Scope §1.4 (`realcheck.go`, `Output.Raw`, `floored`/`cache.floor`,
  `Obj.SetResourceVersion`, `ObjList` accessors); tests (`realcheck_test.go`, `realfacts_test.go`,
  `correctness/cmpdiff_test.go`); translation (project k8s-apiserver: `./correctness`, go-cmp's
  `cmp` names only but `Option`/`applicableOption`, std `maps` names only).
- **Step 0 report pending with the coordinator.** Go: the package and ./correctness green (`/shared/tmp/k8s7g/step0-fulltest.out`); real checker Ok on 5/5 one-member runs and on every failure-free partitioned run (`step0-runs.out`). Lean: the first module that breaks is `KModel` (Output gains `Raw`), `step0-build.log`. Forms decided: `questions.md` (gitignored, local).
- Next, after the coordinator's answer: step 1, the trust-spec texts (HARD STOP: present each with
  its Go evidence before use): `reflect.DeepEqual` (deepRep), `cmp.Diff`, `maps.Keys/Clone/Equal`,
  `slices.Sorted`, maybe `meta.SetList`, `apierrors.SuggestsClientDelay`. Then steps 2-6 (Scope §5).
- Open: the driver's Lean proofs do not build against the new translation until step 5 (so the
  branch cannot land before step 5, unless split); `etc/gen-init.py --check` needs `IsPkgInit`
  instances of `correctness`, `maps`, `cmp` (Lean) and regenerated driver init/PkgTable files.
- Pitfalls:
  - goose's config path for `github.com/google/go-cmp/cmp` is `Code/github_com/google/go_cmp/cmp.toml`
    (underscore), not `go-cmp`.
  - In partitions most runs have a failed call, so the real checker runs in few of them (2 of 10
    partitioned runs failure-free, `/shared/tmp/k8s7g/step0-runs.out`).
  - `cmp.Diff` and `reflect.DeepEqual` tell nil from empty slices.
- Go runs: `cd examples/k8s/etcd3; GOWORK=off systemd-run --scope -q -p MemoryMax=32G go test
  -count=1 -v -run '^TestRealChecker$' .` (and `TestRealCheckerPartition`, `K8SETCD3_SCHED`).

## History

- Scope and Go experiment `ecf71b5f6a`; experiment patch `notes/k8s-7g-experiment.patch`
  (scratch only; its switches are gone from the real driver); nonissue
  `k8s-correctness-watchvalidator-cut-before-bookmark`.

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
