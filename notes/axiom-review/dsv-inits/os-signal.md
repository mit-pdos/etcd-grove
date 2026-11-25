# Axiom review: `os/signal`'s package initializer (`os.signal.wp_initialize'`)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` at `23a50393f5` (the brief named branch `dsv-fix3`; the worktree's
branch was `dsv-fix2b`); Perennial `fce59af75`; Go at the pinned toolchain go1.27.3
(`src/os/signal/signal.go`, `signal_unix.go`).

## The axiom

`Perennial.os.signal.wp_initialize'` (`Dsverify/Proof/os/signal/Init.lean`; the class `InitHyp` there
states the same triple):

    ∀ g, GetIsPkgInitProp pkg_id.os.signal g →
    {{ ownInitializing g }} initialize' #() {{ RET #(); ownInitializing g ∗ isPkgInit pkg_id.os.signal }}

- The translation (`Dsverify/Code/os/signal.lean`, config `signal.toml`: `translate = ["!*"]`,
  `imports = ["!*"]`) is names and types only. Its `initialize'` is
  `package.init pkg_id.os.signal (λ_. exceptionDo (doExecute (@! init.«0» #())))`: the one `init`
  function, called by name (resolved through the context's opaque `functions` table); no package
  variable is allocated or initialized; `PkgInfo.pkgImportedPkgs := []`.
- The package fact (`Dsverify/Proof/os/signal/Base.lean`): `define_is_pkg_init iprop(True)` with no
  imported packages, so `isPkgInit pkg_id.os.signal` is `□ True ∗ □ True`.
  `GetIsPkgInitProp pkg_id.os.signal g` is `g pkg_id.os.signal = isPkgInit pkg_id.os.signal ∧ True`.

So the axiom's whole content is: running the initializer (once, or a no-op on a second call, by
`package.init`'s check) returns `#()`, does not panic or get stuck, touches no resource the caller
owns (the frame rule), and leaves `ownInitializing g` with `os/signal` recorded with the fact `True`.

The Go initializer (go1.27.3): package variables `handlers` (a struct of a `sync.Mutex`, a nil map,
an array and a nil slice), `watchSignalLoopOnce sync.Once`, `watchSignalLoop func()`, all zero
values; `init()` in `signal_unix.go:27-29` is `watchSignalLoop = loop`. Go initializes `sync`,
`syscall`, `context`, `os` (and `slices`) first.

## Verdict: **survives**

## Attacks tried

1. **A false package fact.** The fact is `True` (no `↦□` of `handlers` or `watchSignalLoop`, no pure
   claim about their values): nothing to read back and contradict. Go side: `GODEBUG=inittrace=1`
   shows `init os/signal … 0 bytes, 0 allocs` and the program runs on.
2. **A missing premise (the initializer panics).** `init()` is a single assignment of a function
   value to a package variable; zero-value variable initialization cannot fail. No path to a panic.
   A program importing `os/signal` from two packages and calling `Notify`/`Stop`/`Ignored` exits 0
   (scratch test, below).
3. **Running twice.** Go runs each package's initializers once per program, whatever the number of
   importers (the test: two importing packages, one `init os/signal` line). In the model
   `package.init` checks the package state map and returns `#()` on a second call; the axiom's post
   is the same `ownInitializing g`, so nothing is duplicated (`isPkgInit` is persistent and `True`).
4. **The import table.** The precondition requires nothing of `context`, `os`, `sync`, `syscall`,
   `slices` (the translation's `pkgImportedPkgs` is `[]`). Harmless here: the fact claims nothing that
   depends on them, and Go's initializers of those packages (which Go runs before `os/signal`'s) do
   not panic (they run in every Go program using `os`). A spec that needs one of those packages
   initialized asks for its `isPkgInit` itself, not through `os/signal`'s.
5. **Too much ownership / effects beyond the frame.** The real `init` writes only `watchSignalLoop`,
   an `os/signal` package variable that the names-only translation never allocates, so no Lean
   proof holds a points-to to it; the framed resources are untouched in Go as in the axiom.
6. **Cross-world entailment** (`crossWorld` check): the fact is `True`, with no points-to cells and
   no opaque function of a pointer: not applicable.
7. **Interaction with the package's other specs.** `Dsverify/Proof/os/signal/Spec.lean`'s `Notify`
   specs take `isPkgInit pkg_id.os.signal` as a precondition, but it gives them nothing (`True`);
   their content is the environment premise `NoSignals` (a class, reviewed separately, not here).
   Go's `Notify` relies on `init` having set `watchSignalLoop` only to start the delivery goroutine;
   without it there is no panic either.
8. **Inconsistency (`⊢ False`).** The triple concerns the opaque `functions "os/signal.init.0" []`;
   no lemma fixes that value, so it cannot be refuted in a fixed context. The axiom is stated for
   every Go context (`GoGlobalContext`, `go.Semantics`, `GoSemanticsFunctions`), and would be false
   in a context where `init.0` resolves to a panicking body; but Perennial has no concrete instance of
   these classes (`grep`: none), and this is the trust every interim initializer axiom of the
   repository takes (`notes/dsv-instances.md`, "satisfiable only in the contexts where the names
   resolve to Go's code"). Not specific to this axiom.

Go check (scratch, not committed): module `sigtest` with packages `a`, `b` importing `os/signal`
and `main` calling `signal.Notify(c, SIGUSR1)`, `signal.Stop(c)`, `signal.Ignored(SIGUSR1)`, run at
go1.27.3: prints `a.init`, `b.init`, `main returned normally; Ignored(SIGUSR1)= false`, exit 0;
`inittrace` shows `sync`, `syscall`, `context`, `os`, then `os/signal` once, 0 allocations.

Not tried: a Lean counterexample (no gap found to build one on); the derivation in
`InitInstancesLinked.lean` (its local axiom `localInitFuncsOk` restates the same claim per `init`
function and is test-only).

## Proposed restatement

None. To retire it, as the file header says: translate `signal_unix.go`'s `init` (one assignment)
and the three variables, and prove `wp_initialize'`.

No Go bug found.
