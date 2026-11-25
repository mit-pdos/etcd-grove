# Axiom review: `io/ioutil`'s initializer (`io.ioutil.wp_initialize'`, dsverify quepaxa)

**Retired** (2026-11-25, branch `dsv-retire-1-inits`, mit-pdos/etcd-grove#49): the axiom is gone;
`Discard` (`var Discard io.Writer = io.Discard`) is translated with its import `io`
(`Dsverify/Code/io/ioutil.toml`), and `wp_initialize'` is a theorem, proved in the generated
`Dsverify/Proof/io/ioutil/Init.lean` (it loads `io.Discard` from io's fact `#HDiscard`).
The review below is of the axiom as it was.

Reviewed 2026-11-25 by the `axiom` skill (independent reviewer), on branch `dsv-fix3` at
`1b249c5399`; Go: the standard library of go1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`),
`src/io/ioutil/{ioutil.go,tempfile.go}`.

## The axiom

`Perennial.io.ioutil.wp_initialize'` (`Dsverify/Proof/io/ioutil/Init.lean`; the same statement as
the field of the class `InitHyp` in that file):

    ∀ g, GetIsPkgInitProp pkg_id.io.ioutil g →
      {{ ownInitializing g }} initialize' #() {{ RET #(); ownInitializing g ∗ isPkgInit pkg_id.io.ioutil }}

- `initialize'` (`Dsverify/Code/io/ioutil.lean`, names only, `ioutil.toml`: `translate = ["!*"]`,
  `imports = ["!*"]`) is `package.init pkg_id.io.ioutil (λ_. exceptionDo (doExecute (Discard.init #())))`,
  with `Discard.init` an `opaque val`; `pkgImportedPkgs := []`.
- The package fact (`Base.lean`): `define_is_pkg_init iprop(True)`, so `isPkgInit io.ioutil` is
  `□ True ∗ □ True` (no dependencies, no user fact). `GetIsPkgInitProp` (`build_get_is_pkg_init_wf`)
  only says `g "io/ioutil" = isPkgInit io.ioutil`.
- Users: `raxos/configuration`'s generated `Init.lean` (`initLb_of_spec … ExternalInit.io_ioutil
  wp_initialize'`), and through it the quepaxa kit's programs (`etc/dsv/quepaxa.py`, `HYP_INITS`).
  `InitInstancesLinked.lean` (test only) derives the same statement from the local axiom
  `localOpaqueInitsOk` (`Discard.init #()` returns) via `wp_package_init_lb`, the derivation a
  translated package would get.

Claims, in plain words: (1) running `io/ioutil`'s initializer, from any initialization state,
returns without panicking; (2) it keeps `ownInitializing` (the initialized-packages map, monotone);
(3) afterwards the package's fact holds, which is `True`.

## Verdict: **survives**

The axiom carries essentially no content beyond "the initializer terminates without a panic": the
fact it establishes is `True`, and nothing in the repository gives `Discard.init` or any `io/ioutil`
function a spec (grep: only the test-only `localOpaqueInitsOk` names `Discard.init`; no spec of
`ReadFile`, `ReadAll`, `Discard`, ...; `configuration.NewInstanceConfig`, the kit's only caller of
`ioutil.ReadFile`, is not reached).

## Attacks tried

1. **The fact claims something the initializer does not establish.** The fact is `True`; nothing
   to falsify. The real initializer (`ioutil.go:106`, the package's only package-level variable,
   no `func init` in either file) is `var Discard io.Writer = io.Discard`: a read of `io`'s
   variable, no allocation that can fail, no panic path. Go check (go1.27.3): a program importing
   `io/ioutil` starts, `ioutil.Discard == io.Discard` holds, `Discard.Write` returns 2. Output: `ok 2`.
2. **Missing imports in the precondition.** Real `io/ioutil` imports `io`, `io/fs`, `os`, `slices`,
   `strings`, and its initializer reads `io.Discard`; the model's `pkgImportedPkgs` is `[]`, so
   `GetIsPkgInitProp` does not require `io`'s fact. Harmless: Go always initializes `io` first (the
   language's import-order rule), so the real initializer cannot observe an uninitialized `io`, and
   the axiom's post claims nothing about `io` (or any other package); no proof can derive `io`'s
   fact from `isPkgInit io.ioutil`.
3. **Runs twice.** `initialize'` is wrapped in `package.init pkg_id.io.ioutil`, whose semantics
   (Perennial's `wp_package_init`) skips the body when the package is already marked; the axiom
   gives the same post either way and the post is `True`, so a second call proves nothing new. Go
   runs it exactly once.
4. **`ownInitializing` returned unchanged.** The post's `ownInitializing g` is existential over the
   map, the same form Perennial's proved initializers have; `initLb_of_spec` (proved, monotone ghost
   map) is what callers use to keep lower bounds. No extra resource is created.
5. **Consistency / the opaque `Discard.init`.** The axiom implies `Discard.init #()` is safe (when
   the package is not yet initialized). `Discard.init` is an opaque constant with no other law
   (the local test axiom says the same thing), so a derivation of `False` would go through for any
   value, including `λ_. #()`, for which the triple is provable (`InitInstancesLinked.lean`'s
   derivation shape): no inconsistency. The axiom is stated for every `GooseExts`/`GooseSemantics`/
   `go.Semantics` instance, as Perennial's own proved `wp_initialize'` theorems are.
6. **Cross-world entailment.** No entailment with a pure conclusion about a pointer: the post is
   `True` and `ownInitializing`. Not applicable.
7. **Package-fact clash.** `pkg_id.io.ioutil` has one `IsPkgInit` instance (`Base.lean`); neither
   Perennial nor the main tree translates `io/ioutil`, so no second instance with a different fact
   can be imported beside it.

Not tried: a Lean counterexample (no Go panic exists to build one from); building
`InitInstancesLinked.lean` (the brief forbids larger builds; it is the test-only non-vacuity
derivation and is unchanged by this review).

## Note

If a later change gives `io/ioutil` a non-`True` fact (e.g. `Discard`'s cell `↦□ io.Discard`), the
precondition should then also require `io`'s fact (`imports` in `ioutil.toml`), since the real
initializer reads `io.Discard`; and specs of `ReadFile` etc. would need their own review.
