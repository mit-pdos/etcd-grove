# fmtmodel's review findings: `wp_Errorf_setArgs`, `fmt.argOk`'s `reflect.Value`, `Printf`'s result (2026-11-20)

Found while moving this repository's `fmt` specs onto Perennial's new `fmt` model (Perennial
`79517dbdf`, "fmt: Sprintf, Printf and Errorf call the arguments' Error()/String() as Go does; Errorf
formats and wraps %w"), by reading go1.27.3's `src/fmt` and by the adversarial review of the model (a
subagent with Go's source, the model transcribed to Go, and differential tests and fuzzing:
`goose/model/fmt/model_diff_test.go` in Perennial). No Lean counterexample was built.

## `cache.wp_Errorf_setArgs`: **false as stated, fixed**

`Proof/k8s_io/client_go/tools/cache/ErrorfSet.lean` was a lemma proved over Perennial's previous model of
`Errorf` (`errors.New(format)`, the arguments ignored): `fmt.Errorf(format, args...)` with
`sets.Set[string]` arguments returns, with precondition `isPkgInit ∗ args_sl ↦* args` only, no ownership of
the maps. Go reads each map (`printValue`'s `reflect.Map` case, `fmt/print.go:793-815`, `fmtsort.Sort`), and
a map read concurrent with a write is the runtime's fatal `concurrent map read and map write`
(`internal/runtime/maps/map.go:432`), not recoverable. So a program whose other goroutine writes the map
while `addIndexers` formats it dies in Go, while the lemma (with the map's points-to held by the writer)
proved the call returns. Not reachable in client-go (`addIndexers` formats the fresh intersection it
owns), but the statement was false.

Fix: an axiom now (Perennial's new model is stuck on reflection into a map), whose premise takes a
fraction of each map's points-to and whose post gives it back; its one caller passes the intersection's.

## Perennial's `fmt.argOk` (was this repository's `fmt.argOk`): `reflect.Value` under a method verb

The premise admitted, in its `String()` case, any value with `String() string`, no `Format` and no `Error`:
a `reflect.Value` among them. Go's `printArg` unwraps a `reflect.Value` (`case reflect.Value:`,
`fmt/print.go:734`) and formats the value it holds, calling that value's methods (its `Format`, `Error`,
`GoString`, ...) or reflecting into it, none of which the premise constrained. No caller passed a
`reflect.Value`. Fix (in Perennial, before landing): the `String()` case requires no method named
`CanInterface` (which `reflect.Value` has), and the model is stuck on such a Stringer.

Also from the review: the model's `Printf` returned `(0, nil)`, where Go returns the bytes written (and the
write's error); the model now returns an arbitrary count and `nil` or an arbitrary error. The specs said
nothing of either result, so no statement here changed.

## `fmt.argsOk` no longer admits slices

This repository's `fmt.argsOk` admitted read-only slices of admitted values under `%v`/`%s`
(`fmt.sliceArgOk`). Perennial's model is stuck on reflection into a slice, so its `fmt.argsOk` does not. The
three calls with slices (`ConditionsAwareDecisionUnion.Add`, `unionAuthzHandler.EvaluateConditions`,
`UnconditionalPartsOrFailClosed`) now rest on the narrowed axioms `fmt.ErrorfSlice`/`fmt.SprintfSlice`
(`fmt.argsOkSl`, the old premise), and `fmt.ErrorfStrs` (`[]string` under any verb, `fileutil`) is an axiom
again: they were proved over the previous model, which ignored the arguments, i.e. trusted through it.
