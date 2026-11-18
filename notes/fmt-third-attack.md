# fmt soundness: the third independent attack (2026-11-18)

Axiom skill, read-only, on `fmt.Errorf.spec` after 0a5f7fbe4c (`%#w` sharpV), `fmt.errArgsWf` and
`fmt.ErrorfErrs/ErrorfErrsNot/ErrorfErrsTerm`, `fmt.ErrorfWrap`, the writer contract's error arm. Go
programs `/shared/tmp/fmtfix-attack3/` (go1.27.3); each refutation dies with `fatal error: concurrent map
iteration and map write` (fmt reflects into a caller-owned map the spec does not grant).

- **R1, trailing `.` (refutes `fmt.Errorf.spec`, `fmt.Printf`, `ErrorfPlain` and the drafts
  `ErrorfErrs/Not/Term`).** Go's `doPrintf` (`fmt/print.go:1100`) reads `.` as a precision only if
  `i+1 < end`: in `"x%."`/`"x%5."` the `.` is the verb and consumes the argument (`printArg(e, '.')`:
  no method verb, `printValue` reflects). `fmt.fmtDirectivesAux` goes to `.prec 0` and ends:
  `fmt.fmtDirectives "x%." = some []`, the argument is EXTRA under `%v` and `fmt.argOk`/`fmt.errArgAt`
  admit an error. `trailingdot/` (`fmt.Errorf("x%.", e)`). Fix proposed: in `.flags`/`.width`, a `.` that
  is the last byte is the verb (or the parser returns `none`); test example `"x%."`, `"x%5."`.
- **R2, `%w` of a non-error Stringer (refutes `fmt.Errorf.spec`, pre-existing).** `w ∈ fmt.errorfVerbs`,
  so `fmt.argOk`'s `String()` disjunct is admitted under `%w`; Go's `handleMethods` with `'w'` fails
  `arg.(error)`, `badVerb` reflects. `wstringer/`. Fix proposed: under `w`, only `ArgWf` or the `Error`
  disjunct.
- **R3, `fmt.argOk` checks no signatures (refutes `fmt.Errorf.spec`, pre-existing).** `Error() int`
  that loops meets `fmt.stringMethodSpec` vacuously; Go calls no method and reflects. `badsig/`. Fix
  proposed: `Error`/`String` = `some noArgStringSig` in `fmt.argOk` (as `errOk`/`fmtErrorOk` already).
- No refutation: `errOk`'s type facts, `errIsNot`/`errIsTerm`, `fmt.ErrorfWrap.spec`, the writer
  contract's `errOkOrNil` (real `*os.File.Write` errors checked: `writererr/`).
