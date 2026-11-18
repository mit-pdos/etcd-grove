# fmt soundness 2: `fmt.argOk` under `%w` and its signatures (brief, 2026-11-18)

Follow-up branch `fmt-soundness-2`, off `lean` after `fmt-soundness` lands (decision 8 of
`notes/fmt-soundness-handoff.md`, etcd-grove-03). Approved in principle by etcd-grove-03 (decision 7: stricter
premises only); the old -> new texts go to the user at its land stop.

## The findings (third attack, `notes/fmt-third-attack.md`; programs `/shared/tmp/fmtfix-attack3/`)
- **R2**: `fmt.Errorf.spec` admits, under `%w`, an argument by `fmt.argOk`'s `String()` case (`w ∈
  fmt.errorfVerbs`). Go's `handleMethods` with `'w'` fails `arg.(error)`, `badVerb` reflects into the value
  (`wstringer/`: a concurrent map write makes the runtime throw).
- **R3**: `fmt.argOk`'s `Error`/`String` cases do not say the method is `() string`. An `Error() int` that loops
  meets `fmt.stringMethodSpec` vacuously; Go calls no method and reflects (`badsig/`).
- Not hit by any caller (checked 2026-11-18, `/shared/tmp/fmtfix-check/check.py` over every `Code/` tree: 895
  printf-style calls with literal formats, 1845 arguments with goose's static types; every one of the 77 `%w`
  arguments has static type `error`; no argument's static type has an `Error`/`String` method of another
  signature but bbolt `Options.String`'s `Logger` under `Sprintf`, whose spec is an axiom not using
  `fmt.argOk`; the 7 `%v` arguments of interface type are in functions with no proof, or, `Cacher.get`, a proof
  that does not reach the `Errorf` branch).

## The fix (approved shape)
1. `Spec/fmt/Errorf.lean`: move `noArgStringSig` here from `Spec/fmt/ErrorOk.lean` (it imports Errorf);
   `fmt.argOk`'s `Error` case gains `methodSet ii.ty !! "Error" = some noArgStringSig`, its `String` case
   `methodSet ii.ty !! "String" = some noArgStringSig` (it already has `Error = none`).
2. `fmt.argOkAt`: under `w` only `ArgWf` or the `Error` case (e.g. the method-verb disjunct's pure part gains
   `d.verb = W8 119 → methodSet ii.ty !! "Error" = some noArgStringSig`); adjust `fmt.argOkAt_of_argOk`,
   `klog.argOkAt_of_argOk` and the macros `fmt_args_ok`/`fmt_arg_method` (a `fmt_method_sig` beside
   `fmt_method_none`, by `rfl`/`decide` on goose's method sets).
3. The producers gain the signature fact (a typing fact: every non-nil Go `error` value's dynamic type has
   `Error() string`): `statusErrOk` and `errStrOk` in `Proof/go_etcd_io/etcd/cache/v3/Base.lean`, `errStrOk` in
   `Proof/net/http/Boundary.lean`. Their definitions change the meaning of the axioms whose posts give them.

## Cost (counted 2026-11-18)
- Files mentioning `statusErrOk`: 149; `errStrOk`: 77; `http.errStrOk`: 31. Files with an `axiom` that mention
  one of them: ~30 (each a trusted text whose meaning changes: list them with old -> new at the land stop).
- Sites unfolding them: `statusErrOk` 21 in 13 files, `errStrOk` 24 in 16, `http.errStrOk` 17 in 10.
- Files using `fmt_args_ok`/`fmt_arg_method`/`argOkAt_of_argOk`/`fmt_args_intro`: 37 (21 the two macros).
- `String()` producers of concrete types (`time.Duration`, raft/rafthttp ids and versions): by `rfl`.

## Then
Independent attack (axiom skill) on the new texts; full pipeline as for `fmt-soundness` (build slot, gen-link all
modes, term gate, tcb/collections `--check --update`, interfaces, gates), and the differential test
(`/shared/tmp/fmtfix-diff/`) re-run if the parser is touched.
