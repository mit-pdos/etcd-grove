# apierrors-fix: the restated NewConflict / NewInternalError texts (2026-11-17)

Stage `apierrors-fix` (HasStatusCause fix (a), `notes/hasstatuscause-later-view.md`) gives the two
constructor axioms' posts the details (`statusDetailsAt`). The texts were attacked independently
(etcd-grove-03's attack agent; report and Go program `/shared/tmp/apierrors-attack/cx`).

## Round 1 (texts of 6116eaf7bf): both refuted, one cause

- `NewConflict.wp_proof`, no precondition (the old text too): **false**. Its message formats `err`
  with `%v`; `fmt`'s `catchPanic` recovers a panic in `Error()` but re-panics when the recovered
  value's own `Error()` panics (go1.27 `fmt/print.go:591-594`). `NewConflict(gr, n, nestErr{})`,
  whose `Error()` panics with such a value, panics. A type with `Format` panicking the same way
  (`fmtErr`) too: `handleMethods` calls `Format` in place of `Error()` (`print.go:630-634`).
- `NewInternalError.wp_proof` with the new precondition (`err` non-nil, `fmt.stringMethodSpec ei
  "Error"`): **false**. `fmtErr`'s `Error()` returns, so it meets the precondition, but the message's
  `%v` calls its `Format`, which panics nestedly. (The old text, without precondition, was already
  false: `err.Error()` on `nil`.)
- The details clauses (`statusDetailsAt st []`, `statusDetailsAt st [c]` with `c.Type' = ""`)
  **survive**.

Go: `/shared/tmp/apierrors-attack/cx/cx_test.go` (out: `NewConflict(nestErr)`, `NewConflict(fmtErr)`,
`NewInternalError(fmtErr)` panic; `NewInternalError(simpleFmt)`, a plain panicking `Format`, does
not). In the repository as `examples/premisefix/apierrorsdetails` `TestNestedPanics`.

## Round 2 (decided by etcd-grove-03)

- `NewConflict`: precondition `fmt.argOk err` (`Spec/fmt/Errorf.lean:157`: `nil`, or no `Format` and
  an `Error()` with `fmt.stringMethodSpec`); the docstring's claim that `fmt` recovers a panicking
  `Error` is gone. Callers (the daemonset apimodel) pass `errors.New` errors.
- `NewInternalError`: precondition adds `⌜methodSet ei.ty !! "Format" = none⌝` (as `kErrOk`).
  Callers: `transformErrorToEvent` (via `kErrOk`), the apimodel (via `errors.New`).

Bug record of the old texts: `notes/apierrors-new-precondition.md`.
