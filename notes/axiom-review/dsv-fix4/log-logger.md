# Axiom review: `log.Default` and `*log.Logger`'s `Printf`/`Println` (dsv-fix4)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`) at `a28755b089`; Perennial `fce59af75`; Go at the
pinned toolchain go1.27.3 (`src/log/log.go`, `src/fmt/print.go`). Read-only review: the brief allowed
no branch, translation or Lean file in the repository, so the counterexample is a Go test (run) and a
Lean proof argued below, not machine-checked.

## The axioms

- `log.Default.wp_proof` (`Dsverify/Proof/log/Default.lean`):
  `{{ isPkgInit log }} log.Default #() {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }}`.
- `log.Logger.Printf.wp_proof` (`Dsverify/Proof/log/Logger__Printf.lean`): for `l ≠ null`,
  `{{ isPkgInit log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }} l.Printf msg arg {{ RET #(); arg ↦*{dq} xs }}`.
- `log.Logger.Println.wp_proof` (`Logger__Println.lean`): the same without the format string.

`argOk v` (`Dsverify/Proof/github_com/despreston/go_craq/Craq/LogHyp.lean`) is: `nil`, or
`fmt.ArgWf` (a predeclared basic type), **or a value of any type with neither an `Error` nor a
`String` method** (`typeSetContains ty go.error = false ∧ typeSetContains ty fmt.Stringer.ty = false`),
or `models_lab.errAny v` (an error whose `Error()` has a WP returning some string; nothing about its
other methods).

Claims, in plain words: `Default` returns non-nil; `Printf`/`Println` on a non-nil logger never panic,
read the argument slice only, and **touch no memory the caller owns** (the frame rule: the post gives
back only the slice), for every `argOk` argument.

## Verdict: **refuted** (the two method axioms, as stated; `log.Default.wp_proof` survives)

The false claim: "`fmt` calls no method of an argument but `Error()` of an error" (the header of
`Logger__Printf.lean`). Go's `fmt` (`print.go`, `handleMethods`) calls, before `Error`/`String`:

- `Format(f, verb)` of any argument implementing `fmt.Formatter`, under **every** verb (Println's
  `%v` included);
- `GoString()` under `%#v`, for a `fmt.GoStringer`;
- and, through `printValue` (`depth > 0`, `CanInterface`), the same methods of the exported fields
  of a struct, of the elements of slices/maps, and of the pointee of a top-level pointer.

`argOk`'s third disjunct admits any type without `Error`/`String`, so it admits a type whose `Format`
or `GoString` is arbitrary code; `errAny` admits an error type with a `Format` method. That code may
write memory the caller owns (which the frame keeps unchanged in the proof) or panic in a way
`catchPanic` does not recover (a nested panic: `catchPanic` re-panics when printing the panic value
itself panics).

### The program (Go, run)

    type T struct{ p *int }                       // no Error, no String: argOk holds
    func (t T) Format(f fmt.State, c rune) { *t.p = 1 }

    func MainPrintf() {
        x := new(int)
        log.Default().Printf("%v", T{p: x})
        if *x != 0 { panic("Format wrote memory the caller owns") }
    }

Test (`/shared/tmp/axrev-loglogger/logcx`, scratch, deleted after the review; `GOTOOLCHAIN=go1.27.3`),
every variant panics, deterministically:

    Printf+Format:      PANIC: Format wrote memory the caller owns
    Println+Format:     PANIC: Format wrote memory the caller owns     (log.Default().Println(T{p: x}))
    errAny+Format:      PANIC: ... (E with Error() string { return "e" } and the same Format; errAny holds)
    %#v+GoString:       PANIC: ... (G with GoString() writing *p; no Error/String)
    %+v field Format:   PANIC: ... (S{F T}: S has no methods; fmt calls the field's Format)
    nested panic:       PANIC: again (P.Format panics with U{}, U.String panics: catchPanic re-panics)
    TestUnrecovered:    panic: Format wrote memory the caller owns [recovered, repanicked] -- FAIL

### The proof (argued, not built)

`{{ isPkgInit log }} MainPrintf #() {{ RET #(); True }}`: allocate `x ↦ 0`; `log.Default.wp_proof`
gives `l ≠ null`; build the one-element slice `[mkOk T.ty v]`; `argOk` by its third disjunct, whose
two facts `go_type_set` proves from the generated `MethodSetIs` of `T` (as craq's `meta_noErr`/
`item_noStr` in `Craq/Node/UpdGhost.lean` do; goose records `Format` in the method set, which does not
contain `Error` or `String`), via `argOk_noMethods` (`Craq/Node/Log.lean`); apply
`log.Logger.Printf.wp_proof` framing `x ↦ 0`; load `0`; the `if` is not taken. The nested-panic
variant is even shorter (no frame needed: the axiom's triple excludes the panic Go raises). Its
`#print axioms` would show `log.Default.wp_proof`, `log.Logger.Printf.wp_proof` and the generic ones.

### Also reached without these axioms: Perennial's trusted `log` model

`Perennial/TrustedCode/log.lean` models the package-level `log.Printf`/`log.Println` as
`λ: "format" "vs", #()`, with no argument condition. Perennial's own spec (`Spec/log/Printf`) asks for
`fmt.ArgsWf`, but the model's body is what a proof unfolds: this repository's
`LogHyp.wp_Printf`/`wp_Println` (`LogHyp.lean`, `wp_start; wp_end`) prove the same triples for
`argOk` arguments, so `log.Printf("%v", T{p: x})` followed by the check is provably safe from the
trusted model alone. The no-op model is faithful only for arguments `fmt` formats without calling
user code (Perennial's `fmt/Args.lean` `argOk` gets this right: it requires `Format = none`, and
`stringMethodSpec` for `Error`/`String`). This is a Perennial finding (`notes/perennial-changes.md`):
the model should take `fmt`'s argument condition (e.g. be stuck on an argument outside it), or the
docstring should state that callers must stay within it and the repository's `wp_Printf`/`wp_Println`
must not rely on unfolding it.

## go-craq meets the missing conditions

Not a bug in the verified Go code. go-craq's log arguments (`node/node.go`, `coordinator/
coordinator.go`): strings, `uint64`s, `*store.Item` (`Version uint64, Committed bool, Value []byte,
Key string`) and `*transport.NodeMeta` (bools, strings) under `%+v`/`%#v`, whose fields have no
methods; and errors (`%v`, `%#v`, `err.Error()`) from `net/rpc`, `net`, `gob`, `errors.New`,
`fmt.Errorf` and its own sentinels, none of which has `Format` or `GoString` (`%#v` of `*net.OpError`
prints nested pointers as addresses, calling nothing). So the closed craq results are not falsified
by this gap, provided the errors the models hand back (`errAny`) stand for such types.

## Proposed restatement (not applied)

Tighten `argOk` (and so the axioms' premise), not the axioms' shape:
- third disjunct: also `methodSet ty !! "Format" = none` and `methodSet ty !! "GoString" = none`, and
  restrict it to types whose formatting reaches no method: a basic-kind type, or a struct/pointer to a
  struct whose exported fields are such types recursively (craq's `Item`/`NodeMeta` qualify); simplest,
  name craq's two pointer types explicitly;
- `errAny` disjunct: add `methodSet e.ty !! "Format" = none ∧ methodSet e.ty !! "GoString" = none`
  (or a `stringMethodSpec`-style WP for each, as Perennial's `fmt` `argOk` does);
- better: reuse Perennial's `fmt` argument predicate (`Perennial/Proof/fmt/Args.lean`) extended with a
  case for method-free structs, so `log` and `fmt` share one statement of what `fmt` calls.
The headers' sentence "`fmt` calls no method of an argument but `Error()`" must go.

## Attacks tried that fail

1. **`Default` returns nil** — `log.go:87` `var std = New(os.Stderr, "", LstdFlags)`, never reassigned
   by `log` itself; `Default()` returns it. Only `log.SetOutput`/`SetFlags`/`SetPrefix` change its
   fields, never the pointer. Survives.
2. **A nil `*Logger`** — excluded by `l ≠ null`.
3. **`Error()` that panics (not nested)** — recovered by `catchPanic` (`%!v(PANIC=Error method: …)`);
   and `errAny` gives a WP of `Error()` anyway. No panic escapes.
4. **`Error()`/`Format` re-entering the logger** — `output` formats (`appendOutput`) before taking
   `outMu`, so no self-deadlock; a non-terminating call is no counterexample (partial correctness).
5. **A nil pointer with methods** (`(*E)(nil)` whose `Error` dereferences) — `catchPanic` prints
   `<nil>` for a nil pointer receiver. No panic.
6. **Concurrent use** — `output` reads `prefix`/`flag` atomically and writes under `outMu`; the
   pooled buffer is per call. No panic.
7. **Closed or broken stderr** — `Write`'s error is ignored (no panic); a broken pipe on fd 2 kills
   the process with SIGPIPE, an exit by signal, not a panic (not a counterexample by the skill's
   rules; it does not resume with a wrong state).
8. **After `SetOutput`** — only changes `l.out` under `outMu`; a writer that panics would be a
   counterexample, but the program under proof would have to call `SetOutput`, which has no spec
   here (go-craq never calls it).
9. **Unsynchronized reads** — `fmt` reads through a top-level pointer argument (`%+v` of `*Item`)
   with no permission asked by the axiom; a concurrent writer could in principle tear a slice header.
   Not demonstrated (racy, no deterministic panic); in craq the items are persistent (`itemPtr`).
   Worth closing in the restatement (ask a fractional or persistent points-to of what `fmt` reads).
10. **Cross-world entailment** — no entailment from bare points-tos to a pure fact: not applicable.

Not tried: a machine-checked Lean counterexample (needs a Goose project and a proof file, outside a
read-only brief); the `axiom/<slug>` branch of the skill's step 5 is left for whoever applies the
restatement.
