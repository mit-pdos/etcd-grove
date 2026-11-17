# k8s 7g (the maintainers' checker): handoff

## START HERE

- Branch `k8s-7g` (worktree `/shared/etcd-grove-k8s7g`); lean 3cd4b72599 merged. Pin c6b39d4f8:
  `--packages=/shared/tmp/manifest-c6b.json`; `.lake/package-overrides.json` is that manifest.
  Scope (approved): `notes/k8s-7g-scope.md`. Decisions: `questions.md` (local; step 2 forms ACCEPTED).
- Done: step 0 `e9bf69f83a`/`47eae5838c`; step 1 `11962185aa`/`50faaad1a3`; step 2 `2e775cc56e`.
- **Step 3 in progress** (Go proofs of `correctness`, one spec per function over `RM`):
  - `correctness/Defs.lean` (vocabulary), `ItemsRO.lean` (itemsRO lookup/insert/delete/empty/dom).
  - Proved (no sorry): `keyInScope`, `checkKey`, `GetReadConsistency`, `ListReadConsistency`,
    driver `Obj.DeepCopyObject`/`Obj.SetResourceVersion`; `NewEmptyModel`, `Model.Clone`
    (`730a35dc0e`), `Model.Equal` (`4419c6a1d1`).
  - `Model.get` proved (`54887034bf`; Lean premises on `opts`, ACCEPTED); `Model.create` proved
    (`Defs`: `createObjL`, `optObjD`, `changeRep`; `iapply wp_fupd` before the last call lets the
    final `*Change` points-to be persisted).
  - **Decided (A), user 2026-11-17**: Perennial's `Sprintf` model gets `%v` of a string as `%s`
    (a Perennial branch); after the pin moves, prove `update`/`delete` (precondition branch) and
    `execute`. Until then do NOT prove update/delete/execute (questions.md "Step 3 STOP").
  - `Model.validCacherContinue` proved (over `listItems.spec`; `predOk_driver`'s `Empty` triple, `opts`
    made persistent and split). `listItems.spec` and `list.spec` stated (questions.md, Step 3 forms).
  - STOP 2 decided (etcd-grove-03, questions.md): (a) `maps.Keys.spec_objMap` returns `(f : GoFunc)`,
    (b) `ListAccessor.spec` has an `*ObjList` row (callers of the reflector row use `.1`); applied
    `50be6070ef` (trust delta in `notes/k8s-7g-trust.md` §4, for the joint attack before step 6).
  - `Model.listItems` proved (loop over `ks`, invariant over `itemsOfKeys … (ks.take j)`).
  - Next: `list` (needs a `newObjList` spec/proof, driver, new; `versioner.UpdateList.spec`'s pre
    weakened in place to `metaAtD` — a proved spec; `ListContract.lean` splits `listAtItems`);
    `mlistPCT.wp_proof` for the token. Then `listResponseRV`, `equalListResponse` (ListAccessor `.2`),
    then step-4 bridges not depending on blocked functions.
  - **Blocked until the soundness-1117 fix lands** (V): `validateGet`, `validateList`, `Step`.
- **Standing constraint**: do not touch View.lean / HasStatusCause / IsTooManyRequests /
  SuggestsClientDelay until etcd-grove-03 says the soundness fix (a) + T landed.
- Pitfalls:
  - `RefineList` (and so `PredOk`) builds again (`Raw` added); other driver files past `KWatch` may not.
  - Iris hypothesis with explicit args: `wp_apply HE $$ %_ %DFrac.discard [Pred]`; a struct field of a
    read-only local: `ipersist opts; ihave #o' := opts; iStructNamed o'`; `iunfold` fails on `modelAt`
    (use `modelAt_pkg`).
  - A file whose imports are not built (new Spec imports) hangs lean-check at "elaborating line 1"
    for 30+ min: build the imports first with the build slot, then open it.
  - A fresh file in `etc/lean-check.py` can take 10-15 min (import load + lake building its Spec
    import); then edits re-check in seconds. Keep the file open and iterate; `/shared/tmp/k8s7g-gl.sh
    FILE LINE:COL` prints a filtered goal.
  - `#versionerV` parses as the `#version` command: write `#(versionerV)`. `go!""` → `([] : GoString)`.
  - Driver specs need `[reg : EtcdGrove.k8s.CompactorRegistry]` (its `isPkgInit` instance), and
    `[driver_sem : ...etcd3.Assumptions]` in proofs (not in `correctness.Assumptions`).
  - Generalize big option values before `wp_auto` (`generalize listOptsV x = opts` with field facts).
  - `@[reducible]` constants (`ConsistencyConsistent`) block `wp_auto` stores: `simp only [...]` them.
  - `W64 0` vs `0`/`0#64` in `if`s from simp: `have h0 : n = 0 := hn0; rw [if_pos h0]`.
  - (older) structure-instance continuation columns; `!a || match` in `fun`; `W64 n` → `n#64` by simp.
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-c6b.json build MODULE...`;
  check: `LAKE_OPTS=--packages=/shared/tmp/manifest-c6b.json etc/lean-check.py --max-open 2 FILE`.
- Go runs: `cd examples/k8s/etcd3; GOWORK=off systemd-run --scope -q -p MemoryMax=32G go test
  -count=1 -v -run '^TestRealChecker$' .`

## History

- Step 2's START HERE (2026-11-17): the pure model in `RModel.lean`/`RReplay.lean` (see the commit
  `2e775cc56e`); `KModel`/`KList` build against `Output.Raw` (its `MDefs.Output_intoVal_inj` was left
  broken and fixed in step 3's first commit).
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
