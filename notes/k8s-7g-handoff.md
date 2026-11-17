# k8s 7g (the maintainers' checker): handoff

## START HERE

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`); lean 3cd4b72599 merged (`d41993afa5`).
  Pin c6b39d4f8: `--packages=/shared/tmp/manifest-c6b.json`; `.lake/package-overrides.json` is that
  manifest. Scope (approved 2026-11-17): `notes/k8s-7g-scope.md`. Decisions: `questions.md` (local).
- Done: step 0 (Go) `e9bf69f83a`, `47eae5838c` (IsPkgInit, gen-init); step 0 report answered
  (questions.md: land 0-5 together; cmp `opaqueInitsOk` accepted; Raw approved; Freeze wording).
- **Step 1 done** (`11962185aa` texts, `50faaad1a3` axioms): reviewed by an independent attack
  (`notes/axiom-review/k8s-7g-trust.md`); axioms added for DeepEqual.spec_k8s, cmp.Diff,
  maps.Keys/Clone/Equal, meta.SetList. `SuggestsClientDelay.spec` REFUTED with the existing
  `HasStatusCause.wp_proof` (apiErrOk does not hold `*st.Details`); fix (a) + T land on a separate
  soundness branch. **Do not touch View.lean / HasStatusCause / IsTooManyRequests /
  SuggestsClientDelay here** until etcd-grove-03 says it landed; then merge lean, restate
  SuggestsClientDelay over the fixed apiErrOk, apply V (text in `notes/k8s-7g-trust.md` §2) with M2.
- `etc/tcb-baseline.txt` not yet updated (needs a full build; the driver breaks until step 5):
  +6 axioms here, +`cmp.opaqueInitsOk`; add `etc/tcb-collections/k8setcd3.txt` lines at step 6.
- **Next: step 2** (pure real model, Scope §5, 800-1300 lines), in
  `Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/correctness/` (`RModel.lean`, ...).
  Plan: `RM` = `{ items : GMap GoString Obj, rv : w64, prefix : GoString, rewrite : GMap GoString
  Bool }` (CompactRV is always 0: no compactions); responses as `(DeepV × DeepV)` (object view,
  error view: `k8sDeep.DeepV`, so the `DeepEqual` calls compare them directly); `rexecL` per op
  (create/update/delete/get/list) from `model.go`, `rvalidateGetL`/`rvalidateListL`, `rstepL`;
  `replayL` (states by RV, changes), `validateWatchL` (`watch.go`). Read `model.go` lines 294-560
  and `replay.go`, `watch.go` before writing; reuse `DObj`/`mstore` vocab only in step 4's bridges.
- Open: the driver's Lean proofs do not build against the new translation until step 5 (KModel:
  Output gains `Raw`); `IsTooManyRequests.spec` is false today (typed nil `*StatusError`).
- Pitfalls:
  - goose's config path for go-cmp is `Code/github_com/google/go_cmp/cmp.toml` (underscore).
  - In partitions most runs have a failed call, so the real checker runs in few of them.
  - `cmp.Diff` and `reflect.DeepEqual` tell nil from empty slices; `meta.SetList` always makes a
    non-nil `Items`.
  - apierrors' `.plain` view does not cover nil or `*StorageError` (proposal V).
  - In a def, `∀ e, … Φ #e` needs `(e : GoInterface)` or instance resolution of `go.Semantics`
    gets stuck; a `Prop` over `go.typeSetContains` goes in a section without `go.Semantics`.
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
