# `%#w`: `fmt.Directive.sharpV` misses it (soundness finding, 2026-11-18)

Found by the second independent attack on the fmt-soundness texts (axiom skill; Go
`/shared/tmp/fmtfix-attack2/sharpw/main.go`, go1.27.3).

`fmt.fmtDirectivesAux` (`Spec/fmt/Errorf.lean`) sets a directive's `sharpV` only for `%#v`
(`sharp && decide (b = W8 118)`). Go's `doPrintf` (go1.27 `fmt/print.go`, fast path ~l.1051, slow path
~l.1146) has `case 'w':` fall through to `case 'v':`, which sets `p.fmt.sharpV = p.fmt.sharp`: under
`Errorf`, `%#w` of an error runs `handleMethods` with `sharpV`, which calls the argument's `GoString()`
(or reflects into it), not `Error()`.

- Case a: `*T` with `Error() string` returning `"t"` (no `Format`: `fmtErrorOk`/`errOk` hold) and a
  `GoString()` writing `*t.p = 42`: `fmt.Errorf("%#w", &T{&x})` writes the caller's `x`.
- Case b: `GoString()` panics with a value whose `Error()` panics: `catchPanic` re-raises, the program
  dies (`panic while printing panic value`).

Affected:
- The fmt-soundness drafts `fmt.ErrorfErrs.spec`, `fmt.ErrorfErrsNot.spec`, `fmt.ErrorfErrsTerm.spec`
  (premise `fmt.errArgsWf`): FIXED on the branch before landing, `fmt.errArgsWf` now also requires
  `W8 35 ∉ format` (no `#` anywhere; the WAL's formats have none).
- **The trusted axiom `fmt.Errorf.spec` (`Proof/fmt/Errorf.lean`)**, pre-existing on `lean`: its premise
  `fmt.argsOk fmt.errorfVerbs` admits an `fmt.argOk` error under `%#w` (`fmt.argOkAt`'s method-verb
  disjunct asks `d.sharpV = false`, true for `%#w`). Case a refutes it the same way. NOT fixed here.
  Proposed fix (needs the coordinator: trusted text): in the parser, `sharp && (b = W8 118 ∨ b = W8 119)`,
  so `%#w` is `sharpV` and excluded wherever `sharpV = false` is asked; then recheck every user of
  `fmt.fmtDirectives`/`Directive.sharpV` (for `Printf`/`Sprintf`, `%#w` is a bad verb: `badVerb` with
  `erroring` set, no method called, so the change only makes their premises stricter).
