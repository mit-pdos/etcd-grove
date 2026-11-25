# Axiom review: `google.golang.org/grpc/codes`'s initializer (dsverify quepaxa)

Reviewed 2026-11-25 by the `axiom` skill (independent reviewer), on worktree
`/shared/etcd-grove-mathrand`, branch `dsv-fix3` at `23a50393f5`; Go: grpc v1.84.0 (the version
`examples/dsverify/quepaxa/go.mod` pins), go1.27.3; Perennial at the manifest's
`/shared/perennial-fce59af75`.

## The axiom

`Perennial.google_golang_org.grpc.codes.wp_initialize'`
(`Dsverify/Proof/google_golang_org/grpc/codes/Init.lean`; the class `InitHyp` there is the same
statement):

    ∀ get_is_pkg_init, GetIsPkgInitProp pkg_id.google_golang_org.grpc.codes get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} initialize' #()
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit pkg_id.google_golang_org.grpc.codes }}

What it claims, in words:

1. the part's `initialize'` (`Dsverify/Code/google_golang_org/grpc/codes.lean`) returns, without a
   panic: it is `package.init codes (λ_. exceptionDo (FuncResolve init.0 #(); strToCode.init #()))`,
   both callees untranslated (`init.0` a function name with no body registered; `strToCode.init`
   an `opaque` value);
2. afterwards the package fact holds. The fact (`Base.lean`) is `define_is_pkg_init iprop(True)`, and
   the translation's `pkgImportedPkgs := []`, so `isPkgInit codes` is `□ True ∗ □ True`: nothing;
3. it needs only `ownInitializing` and the well-formedness of the table, which for a package with no
   imports in the translation is `get_is_pkg_init codes = isPkgInit codes`.

## The Go code

`codes/codes.go` and `codes/code_string.go` at v1.84.0. Imports: `fmt`, `strconv`,
`google.golang.org/grpc/internal`. Initialization:

- `var strToCode = map[string]Code{ "\"OK\"": OK, ..., "\"UNAUTHENTICATED\"": Unauthenticated }`
  (codes.go:204): a map literal of 17 constant keys, no calls; cannot panic.
- `func init() { internal.CanonicalString = canonicalString }` (code_string.go:27): one assignment
  of a function value to a package variable of `grpc/internal`; cannot panic.
- Constants (`OK` ... `Unauthenticated`, `_maxCode`): compile-time.

Run: a program importing `codes` (in the quepaxa module, go1.27.3) initializes it and decodes
`"OK"`, `"CANCELLED"`, `"UNAUTHENTICATED"` through `strToCode` (`json.Unmarshal` into a `Code`):
prints `OK`, `Canceled`, `Unauthenticated`, `init ok Unavailable`, exit 0. (Temporary directory,
removed after the run.)

## Verdict: **survives**

The axiom's only content is "the initializer returns", which the Go code meets trivially, and a
package fact of `True`, which no attack can contradict.

## Attacks tried

1. **A false package fact.** The fact is `True` (and the deps' part is empty): nothing to read back
   and check. No pure fact, no points-to, so no cross-world entailment (SKILL step 3) either.
2. **Panic in the initializer.** Neither the map literal nor the one assignment can panic in Go
   (above, and the run). The axiom asserts no more than that (partial correctness: it says nothing
   that a hang would contradict).
3. **Running it twice / concurrently.** `initialize'` is `package.init`: Perennial's
   `wp_package_init` runs the body only when the table says the package is not yet initialized, and
   otherwise returns the stored fact; `ownInitializing` is exclusive, so there is no concurrent
   initialization in the logic. Go runs package init once. A second call in the logic gives only
   `True` again.
4. **Missing imports in the precondition.** The real package imports `fmt`, `strconv` and
   `grpc/internal`; the names-only translation has `pkgImportedPkgs := []`, so `GetIsPkgInitProp`
   requires nothing of them and `isPkgInit codes` carries none of their facts. That is the sound
   direction: no client gets `fmt`'s or `strconv`'s fact through `codes`'s. The initializer's bodies
   in Go touch none of `fmt`/`strconv` (only constants and a map literal) and one variable of
   `grpc/internal`, so no precondition about an import's state is missing for them to return.
5. **The hidden write to `grpc/internal.CanonicalString`.** The real `init` writes another package's
   variable, which the axiom's frame does not mention (the post returns `ownInitializing` and no
   ownership is consumed). Attack: own that variable in Lean, run `codes`'s initializer, read it back
   unchanged. Blocked: `google.golang.org/grpc/internal` is translated nowhere (neither in
   `Dsverify/Code` nor in the main tree's `Code/google_golang_org/grpc/`, which has only
   `internal/status`), so no proof can obtain a points-to of `internal.CanonicalString`; a global's
   cell comes only from its own package's initializer. If `grpc/internal` is ever translated with a
   fact owning `CanonicalString` (e.g. `↦□ nil`), this axiom's frame becomes wrong and must be
   revisited.
6. **Collision with the main tree's `codes`.** The main tree translates `codes` too (with
   `strToCode`'s literal; `Code/google_golang_org/grpc/codes.toml`) under the same Lean names, so the
   two cannot be imported together (duplicate declarations): the axiom cannot be applied to the main
   tree's `initialize'`. (`etc/dsv/quepaxa.py`'s `OWN`.)
7. **Consistency.** `InitInstancesLinked.lean` (test only) derives the statement from local axioms
   saying just that the two untranslated callees return `True`, by the same walk `etc/gen-init.py`
   writes for translated packages; so the axiom adds nothing beyond "these two calls return". Not
   rebuilt here (no build was allowed beyond a single small module; not needed for the verdict).
8. **Callers.** Applied once, in the generated `Dsverify/Proof/raxos/replica/src/Init.lean:113`
   (through `ExternalInit.google_golang_org_grpc_codes`, `Dsverify/Proof/runtime/PkgInitDsv.lean`),
   with `Hinit` projected from the program's package table: nothing beyond the statement is used.

## Caveats (not defects)

- **The general names-only caveat.** The axiom holds for every `GoSemanticsFunctions`: a constructed
  function table with `functions "google.golang.org/grpc/codes.init.0" = <a panic>` (or an
  interpretation of the opaque `strToCode.init` that panics) would falsify it. As for every
  names-only `*.wp_proof` and initializer axiom (`../wal-pb-fmt.md`'s caveat, `notes/status-history.md`):
  the claim is about the real Go program's function table, which no Lean proof can construct today.
- **Model vs Go initialization order.** In the model, `codes`'s initializer does not run `fmt`'s,
  `strconv`'s or `grpc/internal`'s first (the translation drops the imports). Go does. Harmless here
  (the bodies need nothing of them), but it is a property of the names-only translation, not of this
  axiom.

## Not tried

No Lean counterexample was attempted (no gap was found to make one from). `InitInstancesLinked` was
not compiled.
