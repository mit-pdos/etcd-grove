# fmt soundness 2: handoff

## START HERE (2026-11-18, in progress)
- Branch `fmt-soundness-2` (worktree /shared/etcd-grove-fmtfix), off lean 1b298c1e70. Brief:
  `notes/fmt-soundness-2.md` (R2/R3 of `notes/fmt-third-attack.md`).
- Done: the fix in place (below); independent attack round 5 (axiom skill, fresh agent): no refutation.
- Next, in order: full build green (`/shared/tmp/fmtfix2/build*.log`); `etc/gen-link.py` every mode incl.
  `--wal-tester` (after the WAL Link rebuilds), rebuild; term gate; tcb `--check` (no axiom count change
  expected) and collections; interfaces; gates (flock full-build lock, LAKE_PACKAGES=/shared/tmp/manifest-6d3.json,
  PERENNIAL_CHECKOUT=PERENNIAL_DIR=/shared/perennial-6d365ee1a, GOWORK unset); audit rows; STATUS; land stop.
- Pitfalls: every edit of `cache/v3/Base.lean`, `Spec/fmt/Errorf.lean` or `Proof/errors/NewVar.lean` rebuilds
  ~7-14k modules: put helper lemmas in the leaf files. Two `Init.lean`s changed through `etc/gen-init.py`
  (needs `PERENNIAL_DIR=/shared/perennial-6d365ee1a`). Slots are contended: a killed build loses its slot.

## The changed texts (old -> new: `git diff 1b298c1e70`)
Trusted / meaning-changing:
- `fmt.argOk` (Spec/fmt/Errorf.lean): Error disjunct + `Error = some noArgStringSig`; String disjunct +
  `String = some noArgStringSig`. `fmt.argOkAt`: method-verb disjunct + `verb = w -> Error = some noArgStringSig`.
  Premises only (stricter) of `fmt.Errorf.spec`, `fmt.Printf`, klog, `SprintfArgs`, `ErrorfPlain`; positive in the
  posts of `Snapshotter.DBFilePath`, `os.Rename` (axioms; their errors are Go errors).
- Producers gaining `Error() string` (true of every non-nil Go `error` value): `statusErrOk`, `errStrOk`,
  `rpctypesEtcdErrorTy`, `cacheInit`'s ErrUnsupportedRequest clause (cache/v3/Base.lean); `http.errStrOk`
  (net/http/Boundary.lean); `context.errStringOk` (Spec/context/Err.lean, producer proved); `errLeaf`
  (etcdserver/apply/Base.lean), `ctxDeadlineLeaf` (etcdserver/BaseApply.lean), `authErrVar` (auth/Base.lean),
  `leaseErrVar` (lease/Base.lean) (each: last conjunct `Format = none` -> `(Format = none ∧ Error = some sig)`);
  `isEtcdProgressNotifier` (cache/v3/InvEtcd.lean); `bcrypt.GenerateFromPassword.spec`'s post (axiom).
- Classes (proved instances): `ErrorStringLeaf` + `errorSig` (Proof/errors/NewVar.lean; instance premise of the
  closed `auth3_Main`, `authkv_Main`: still discharged by `errorStringLeaf_inst`); `RpctypesEtcdErrorMethods`
  + `errorSig` (generated rpctypes/Init.lean).
- Axioms whose posts now carry the signature fact (attack round 5's list): `status.Error.wp_proof`,
  `types.IDFromString`, `Snapshotter.SaveDBFrom`, `Snapshotter.DBFilePath`, `os.Rename`, bcrypt, v3rpc
  `toGRPCErrorMap_init`, rpctypes `errStringToError_init`, `ErrGRPCNotSupportedForLearner_init`, the
  `ErrGRPC*_init` stating `statusErrOk`, net/http `Axioms.lean`'s `http.errStrOk` posts.

Internal (form): `noArgStringSig` moved to Spec/fmt/Errorf.lean; new lemmas `fmt.argOkAt_of_error`,
`fmt.methodSet_some`, `fmt.argOk_of_fmtErrorOkOrNil`, `fmt.argOkAt_of_fmtErrorOkOrNil`, `errStrOk_methods`,
`errorString_errorSig`; `fmt.argOkAt_of_argOk` takes `verb ≠ w`; macros `fmt_method_facts`, `fmt_verb_ok`.
