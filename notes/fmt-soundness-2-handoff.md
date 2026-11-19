# fmt soundness 2: handoff

## START HERE (2026-11-19, lean df37bd5157 merged at 140f619665 (Perennial pin f551a1b46; conflicts notes only): full timed build green 1st try (build 20261119-034100-1413852, 21791 jobs), gen-init/gen-raft-tla/goose --check ok, all 59 gen-link modes + btree identical, tier-check ok, tcb --check 884/4 = lean baseline, 69 collections, api/interfaces/import-all, errorf gate ok; manifest now /shared/tmp/manifest-f55.json (PERENNIAL_DIR=/shared/perennial-f551a1b46). Before that: the land stop: gates PASSED at ed7fd54098, only this note after it (/shared/tmp/fmtfix2/gates.log); awaiting etcd-grove-03)
- Branch `fmt-soundness-2` (worktree /shared/etcd-grove-fmtfix), off lean 1b298c1e70. Brief:
  `notes/fmt-soundness-2.md` (R2/R3 of `notes/fmt-third-attack.md`).
- Done: the fix in place (below); independent attack round 5 (axiom skill, fresh agent): no refutation; full build
  green (21779 jobs, /shared/tmp/fmtfix2/build6.log); every gen-link mode incl. `--wal-tester`: no Link changed;
  gen-init/gen-raft-tla up to date; term gate ok; tcb `--check` 891 axioms / 4 sorries unchanged; 69 collections
  match; interfaces and api unchanged; audit row; STATUS; gates all passed.
- Axioms whose statement reaches a changed predicate: `/shared/tmp/fmtfix2/axdefs2.out` (117, Lean walk through
  definitions, `/shared/tmp/fmtfix2/axdefs.lean`); post-position heuristic `/shared/tmp/fmtfix2/polarity.out`.
- Pitfalls: every edit of `cache/v3/Base.lean`, `Spec/fmt/Errorf.lean` or `Proof/errors/NewVar.lean` rebuilds
  ~7-14k modules: put helper lemmas in the leaf files. Two `Init.lean`s changed through `etc/gen-init.py`
  (needs `PERENNIAL_DIR=/shared/perennial-6d365ee1a`). Slots are contended: a killed build loses its slot.
  Inline copies of "no Format" facts (a last conjunct `Format = none`) became pairs `(Format = none ∧ Error = sig)`
  so that anonymous-constructor destructurings keep working.

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
- Textual post changes (axioms): `os.Rename.spec`, `snap.Snapshotter.DBFilePath.spec`: `fmt.argOk err` ->
  `fmtErrorOk err`; `bcrypt.GenerateFromPassword.spec`: last-but-one conjunct `Format = none` -> `(Format = none ∧
  Error = some (Signature [] false [string]))`. Premise-side (k8s, not axioms): `pager.pageRes`, `cache.lwOk` (a
  named hypothesis of k8s `Main`), `typedListRet_pageRes`: `fmt.argOk err` -> `fmtErrorOkOrNil err`; `kErrOk`
  (k8s etcd3 WatchDefs) gains the signature.
- Axioms whose posts now carry the signature fact (attack round 5's list): `status.Error.wp_proof`,
  `types.IDFromString`, `Snapshotter.SaveDBFrom`, `Snapshotter.DBFilePath`, `os.Rename`, bcrypt, v3rpc
  `toGRPCErrorMap_init`, rpctypes `errStringToError_init`, `ErrGRPCNotSupportedForLearner_init`, the
  `ErrGRPC*_init` stating `statusErrOk`, net/http `Axioms.lean`'s `http.errStrOk` posts.

Internal (form): `noArgStringSig` moved to Spec/fmt/Errorf.lean; new lemmas `fmt.argOkAt_of_error`,
`fmt.methodSet_some`, `fmt.argOk_of_fmtErrorOkOrNil`, `fmt.argOkAt_of_fmtErrorOkOrNil`, `errStrOk_methods`,
`errorString_errorSig`; `fmt.argOkAt_of_argOk` takes `verb ≠ w`; macros `fmt_method_facts`, `fmt_verb_ok`.
