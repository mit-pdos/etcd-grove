# k8s 7g (the maintainers' checker): handoff

## START HERE

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`); lean 3cd4b72599 merged. Pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json`; `.lake/package-overrides.json` is that manifest.
  Scope (approved 2026-11-17): `notes/k8s-7g-scope.md`. Decisions: `questions.md` (local).
- Done: step 0 (Go) `e9bf69f83a`, `47eae5838c`; step 1 (trust specs) `11962185aa`, `50faaad1a3`
  (reviewed: `notes/axiom-review/k8s-7g-trust.md`); **step 2 (pure real model)**: see below.
- **Standing constraint**: do not touch View.lean / HasStatusCause / IsTooManyRequests /
  SuggestsClientDelay until etcd-grove-03 says the soundness fix (a) + T landed; then merge lean,
  restate SuggestsClientDelay over the fixed apiErrOk, apply V (`notes/k8s-7g-trust.md` §2) with M2.
- tcb-baseline update (+6 axioms, cmp `opaqueInitsOk`) deferred to step 5/6 (accepted).
- **Step 2** in `Proof/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/correctness/`:
  `RModel.lean` (`RM`, `RResp`/`RErr`, `RChange`; `rcreateL`/`rupdateL`/`rdeleteL`/`rgetL`/
  `rlistL`/`listConsL`/`rexecL`; `rvalidateGetL`/`rvalidateListL`/`equalListRespL`/`listRespRVL`/
  `validCacherContinueL`/`listItemsL`; `rstepL`; `absR` = `initialModel`; `sortedKeysL` with
  `sortedKeysL_spec`/`_unique` for `maps.Keys.spec_objMap`), `RReplay.lean` (`replayL`,
  `rvalidateL`, `REv`, `validateWatchL` and its pieces, `realOkL`). Forms: questions.md "Step 2".
  `KModel`/`KList` now build against the `Raw` translation (zero `Raw` in the model's outputs).
- **Next: step 3** (Go proofs of `correctness`, Scope §5: model, replay, watch, consistency; report
  per file). Each spec: the Go function equals its pure function, over `RM` held as a persistent
  `*Model` (`↦□` items map, `mapRep` of the objects, the `NeedsRewrite` map), `Input` given as
  `realRequest(in)`'s value, premises for the unreachable branches (keys prepare, `MinRV` parses,
  list facts of `kInOk`/`WatchInOk`). Needs: `errors.New` → `*errorString` (trust note §3),
  `NewInvalidObjError` post naming the inner error, Sprintf `%v` of strings (R1), the `delay` bit
  of the store's too-large error (step 3/5).
- Pitfalls:
  - structure-instance fields continued on a new line must start at or right of the first field's
    column (else "unexpected identifier; expected '}'"); `prefix`/`rewrite` are keywords.
  - `!a || (match ...)` inside `fun` failed with "Disjoint Bool": write an `if`.
  - simp turns `W64 n` into `n#64`: use `rw [ite_eq_left_of_eq_true _ _ (eq_true h)]` with the
    `W64` hypotheses; `bv_omega` for `n + W64 1 ≠ n`.
  - goose config path for go-cmp is `Code/github_com/google/go_cmp/cmp.toml` (underscore).
  - `cmp.Diff`/`DeepEqual` tell nil from empty slices; `meta.SetList` makes non-nil `Items`.
  - In a def, `∀ e, … Φ #e` needs `(e : GoInterface)`; a `Prop` over `go.typeSetContains` goes in a
    section without `go.Semantics`.
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build
  Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.RReplay`; check:
  `LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
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
