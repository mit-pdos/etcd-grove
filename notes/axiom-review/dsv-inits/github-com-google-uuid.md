# Axiom review: `github_com.google.uuid.wp_initialize'` (dsverify swiftpaxos)

- **Axiom**: `Perennial.github_com.google.uuid.wp_initialize'`,
  `Dsverify/Proof/github_com/google/uuid/Init.lean` (worktree `etcd-grove-mathrand`, branch `dsv-fix3`,
  head `23a50393f5`); the same statement as the class `InitHyp` in that file:
  ```lean
  axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
      (Hinit : GetIsPkgInitProp pkg_id.github_com.google.uuid get_is_pkg_init) :
      {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit pkg_id.github_com.google.uuid }}
  ```
  with, in the same file, the hand-written `isPkgInit_inst` (`isPkgInitDeps := True`,
  `isPkgInitDef := True`) and `get_isPkgInit_wf_inst` (`GetIsPkgInitProp uuid g` is
  `g uuid = isPkgInit uuid ∧ True`: no import constrained).
- **Translation** (names and types only): `Dsverify/Code/github_com/google/uuid.lean`. `PkgInfo`'s
  `pkgImportedPkgs := []`; `initialize'` is `package.init uuid (λ_. jsonNull.init; timeNow.init;
  xvalues.init; NameSpaceDNS.init; …URL; …OID; …X500; rander.init; poolEnabled.init; poolPos.init)`,
  each `X.init` an `opaque` value (`«_».init` is declared but not called).
- **Go**: `github.com/google/uuid` v1.3.1 (`examples/dsverify/swiftpaxos/go.mod`), go1.27.3.
- **Users**: the swiftpaxos kit's boots (`examples/swiftnet/BootLinked.lean:178`,
  `wp_apply github_com.google.uuid.wp_initialize' _ (wf_github_com_google_uuid hk)`); no
  `InitInstancesLinked.lean` for this package.
- **Verdict: survives** (2026-11-25). No counterexample; none exists (below).

## The claim in plain words

1. Run with permission to initialize (`ownInitializing g`), `initialize'` returns `#()` without panic
   and without getting stuck.
2. It gives `ownInitializing g` back (no claim about which packages are recorded initialized) and
   `isPkgInit uuid`, which is `True` (persistent, empty).
3. The only premise: `g uuid = isPkgInit uuid`.

## The real initializer (v1.3.1)

No `func init` and no `var _` in the package. The package-level initializers:

- `hash.go:15-18`: `NameSpaceDNS/URL/OID/X500 = Must(Parse("6ba7b81{0,1,2,4}-9dad-11d1-80b4-00c04fd430c8"))`
  — `Must` panics on a `Parse` error (`uuid.go:178-183`), but the four strings are constant, valid
  36-character UUIDs; `Parse` is deterministic;
- `null.go:14`: `jsonNull = []byte("null")`; `util.go:19`: `xvalues = [256]byte{…}` (a literal);
- `time.go:30`: `timeNow = time.Now`; `uuid.go:40-43`: `rander = rand.Reader`, `poolEnabled = false`,
  `poolPos = randPoolSize`;
- zero-valued: `Nil`, `nodeMu`, `ifname`, `nodeID`, `zeroID`, `interfaces`, `timeMu`, `lasttime`,
  `clockSeq`, `poolMu`, `pool`.

None reads input, the environment or mutable state of another package beyond copying `rand.Reader`
and `time.Now` (initialized first by Go's import order); none can panic. Checked at the pin: a Go
test importing the package (`uuid.NameSpaceDNS`/`X500` equal their strings, `Nil` is zero, `New()`
returns) passes at go1.27.3, and every swiftpaxos program starts.

## Attacks tried

1. **A false package fact.** The fact is `True` (both `isPkgInitDeps` and `isPkgInitDef`), so the
   post claims nothing about the package's variables (not `rander = crypto/rand.Reader`, not
   `poolEnabled = false`, not the namespaces' bytes). Nothing to falsify by reading a variable after
   init. The kit's uuid specs (`lib/LibSpecs.lean`: `New.spec` with pre `isPkgInit uuid`, `UUID.ID.spec`
   with pre `True`) are hypotheses/environment classes (`SwiftHyps.uuid_ID`, `SwiftOsRandom.uuid_New`),
   not this axiom; they gain nothing from it beyond the empty `True`.
2. **A panicking initializer.** The only panic path is `Must` on `Parse`'s error at four constant
   valid strings: unreachable. No `init()` functions. Claim 1 holds of Go.
3. **Missing imports in the precondition.** `GetIsPkgInitProp` constrains only `g uuid`, while Go's
   initializer reads `crypto/rand.Reader` and `time.Now`. In the model, `initialize'` does not
   initialize or read any import (`pkgImportedPkgs := []`, opaque `X.init`s), and the post names no
   import's fact or state, so an uninitialized import in the Lean context cannot turn into a false
   conclusion. Go initializes the imports first regardless.
4. **Running twice / re-entrance.** Perennial's `package.init` (`wp_package_init`,
   `Perennial/Golang/Theory/Pkg.lean:478` at `fce59af75`) returns at once when the package is recorded
   initialized; the axiom's post holds either way (it does not even claim the package is recorded).
   Concurrent runs are excluded by the exclusive `ownInitializing g`. A cyclic re-entry (the
   in-progress state) is impossible in Go (no import cycles) and, uuid importing nothing in the
   model, unreachable in the model.
5. **Inconsistency.** The statement is a WP about a fixed expression built from `opaque` values;
   Lean can prove nothing about their reduction, so no `⊢ False` follows (a model: every `X.init`
   `= λ_. #()`, under which the triple is provable as for a package with trivial initializers). The
   post `isPkgInit uuid` is `True`, so no ghost resource is created from nothing.
6. **Cross-world** (`crossWorld` check): no pure equation about an opaque function of a pointer; not
   applicable.

## Not tried

- The universal quantification over `GooseSemantics`/`GooseExts`/`GoGlobalContext` instances (a
  semantics in which `package.init` or `exceptionSeq` behaves differently) is common to every
  generated `wp_initialize'` axiom of the parts and Perennial's, not specific to uuid; not attacked.
- No Lean counterexample attempted: no Go program panics, so there is nothing to prove.
