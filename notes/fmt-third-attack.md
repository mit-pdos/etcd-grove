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

## The differential test (2026-11-18, decision 7 of the handoff)

`/shared/tmp/fmtfix-diff/`: `gen.py` (2,127,162 formats: every string of length 1-5 over
`% . # + - 0 space 1 9 * [ ] v s w d q x a` with a `%`, every length-6 string over `% . # 0 space 1 9 * v w a +`
with a `%`, 300k random ones of length 6-14 adding `T`, `é`, `\xff` and long digit runs); `gofmt/main.go`
(go1.27.3: `fmt.Errorf(format, 8 probes)`, each probe an error with a `Format` method logging the verb and
`#`); `lean/Diff.lean` (`lake env lean --run`: `fmt.fmtDirectives` of each format, padded with `%v` for the
EXTRA arguments); `cmp.py` (compares; `#` counts only under `v`, as `sharpV`; Go's `%T` calls no method where
Lean has a non-method-verb directive, stricter; an invalid UTF-8 verb is U+FFFD in Go, the byte in Lean,
neither a method verb).

- Before (0a5f7fbe4c's parser): Lean `none` 275,098 (harmless: no premise holds), agree 1,808,943,
  **mismatch 43,121, every one a format ending in a trailing `.`** after `%`, flags or a width (R1).
- After the fix (a `.` starts a precision only if a byte follows it): `none` 275,098, agree 1,852,064,
  **mismatch 0**.

## Round 4 (independent, axiom skill, 2026-11-18): no refutation

On the texts as they land (R2/R3 excluded as known). Parser read against go1.27.3 `doPrintf`/`parsenum`/
`argNumber` (`print.go:1007-1185`): no divergence. Method choice (`handleMethods`, `print.go:614-750`) run over
every ASCII verb byte, `é`, `\xff`, ten flag sets, under `Errorf` and `Fprintf`, three probe types
(`/shared/tmp/fmtfix-attack4/verbs/`): the only `GoString` calls are under `%#v`/`%#w`, where `argOkAt` admits
only method-less `ArgWf`. `ErrorfErrs/Not/Term`, `ErrorfWrap`, the writer contract (`*os.File.Write`'s errors),
`Printf`, klog's args: true of Go. The harness re-checked by an independent Python transcription of the parser
(`/shared/tmp/fmtfix-attack4/harness/py_parser.py`: identical to `lean.after.out` on all formats, 0 mismatches
against Go). Its blind spots, each argued harmless: probes all have `Format` (method choice tested by the verb
run instead); `Errorf` only (same `doPrintf`); Lean `none` skipped (sound); `w` folded into `v` (harmless);
always 8 arguments (`missingArg` does not change parsing); `%p` and the 7/8-digit boundary rarely generated
(checked in the source).
