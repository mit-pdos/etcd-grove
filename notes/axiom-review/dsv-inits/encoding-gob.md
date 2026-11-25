# Axiom review: `encoding.gob.wp_initialize'` (dsverify swiftpaxos, quepaxa)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), on branch `dsv-fix3` of the
worktree `/shared/etcd-grove-mathrand` at `23a50393f5`; Go: the standard library's `encoding/gob` at
the pinned toolchain go1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`); Perennial at the manifest's
`/shared/perennial-fce59af75`.

## The axiom

`Perennial.encoding.gob.wp_initialize'` (`Dsverify/Proof/encoding/gob/Init.lean`; the same
statement is the class `InitHyp`'s field `wp_init`):

    ∀ get_is_pkg_init, GetIsPkgInitProp pkg_id.encoding.gob get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} initialize' #()
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit pkg_id.encoding.gob }}

The claims, in plain words:

1. `initialize'` returns (no panic) from any initialization state.
2. Afterwards `isPkgInit encoding/gob` holds. Its user part is `True`
   (`Dsverify/Proof/encoding/gob/Base.lean`: `define_is_pkg_init iprop(True)`); its dependency part
   `isPkgInitDeps` is built from `PkgInfo.pkgImportedPkgs`, which is `[]` (the translation's
   `imports = ["!*"]`, `Dsverify/Code/encoding/gob.toml`; `Dsverify/Code/encoding/gob.lean:864`). So
   the fact is `□True ∗ □True`.
3. `ownInitializing` comes back (with an unconstrained package map, which is weaker than the proved
   `wp_package_init`'s post).

The translation's `initialize'` (`Dsverify/Code/encoding/gob.lean:869`) is `package.init` of a
body that runs 41 opaque variable initializers (`X.init`, uninterpreted `opaque` constants) then
`FuncResolve init.0/1/2` (names only), and calls no import's `initialize'`.

## Verdict: **survives**

The only content of the axiom is "gob's initializer returns"; the fact it grants is trivial and no
spec reads it. Go's gob initializer has no input and never panics at the pin.

## Attacks tried

1. **Does the real initializer panic?** The Go initializers (go1.27.3 `src/encoding/gob/`): the
   `var` initializers (`errors.New`, `reflect.TypeFor`, `make`, `sync.Pool{…}`, the op tables, the
   `bootstrapType` calls, `tWireType = mustGetTypeInfo(wireTypeType).id`) and the three `init`
   functions (`type.go:280` with `checkId` and the `nextId too large` check, `type.go:940`
   storing `typeInfoMapInit`, `decode.go:1285` with the int/uintptr-size switches). Every panic
   path is a check of constants of the package itself (bootstrap ids, `intBits`/`uintptrBits` ∈
   {32, 64}, a fresh `types` map so no "already present"). `debug.go`, `dump.go`, `decgen.go` are
   `//go:build ignore` (so three `init`s, matching `init.«0..2»`). Run: a program importing gob that
   encodes and decodes a struct, `go run` at go1.27.3 on linux/amd64 and a `GOARCH=386` build:
   both print `gob init ok {1 x}`, exit 0. Any program importing gob runs these at start, so the
   kits' programs (swiftpaxos `swift/defs.go`, quepaxa `common/common.go`) do.
2. **A false package fact.** The fact is `True` plus the empty dependency conjunction: nothing to
   falsify. No spec in `Dsverify/` reads `isPkgInit pkg_id.encoding.gob` for a value (swiftpaxos's
   `Encoder`/`Decoder` specs are its statement's hypotheses, not facts of the initializer).
3. **Run twice.** `initialize'` goes through `package.init`, whose second call sees the package
   marked and returns (Perennial's `wp_package_init`, `Pkg.lean:478`); Go runs the initializer once.
   The axiom's claim (returns) holds for both.
4. **Missing imports in the precondition.** `GetIsPkgInitProp pkg_id.encoding.gob` (built by
   `build_get_is_pkg_init_wf` from `pkgImportedPkgs = []`) constrains only gob's own entry. The real
   initializer touches `reflect`, `sync`, `sync/atomic`, `maps`, `errors`, `fmt`, `os`
   (`checkId`'s stderr) …, but Go initializes them before gob, and the axiom claims none of their
   facts (the translation calls no import's `initialize'`), so nothing about them is asserted that
   their own initializers did not establish. The model omits their initialization; that can only
   make the model know less, not claim more.
5. **Ordering / other packages' effects.** A user package's `init` that calls `gob.Register` with a
   duplicate name panics in Go, but that runs after gob's initializer, in the importer's
   initializer, outside this axiom (it would be a spec of `Register`).
6. **Cross-world (quantification over the semantics).** The axiom is stated for every
   `go.Semantics` instance, whose `functions` maps the names `encoding/gob.init.0..2` to anything
   (gob's `Assumptions` is not even a premise). At an instance where `functions init.2 []` panics
   the triple is false of the model, which would make it inconsistent if a proof could step to that
   call. It cannot: the 41 opaque `X.init` calls run first, and nothing in Lean says what they do
   (they depend only on `GooseExts`/`GoGlobalContext`, are `opaque`, and have no law), so no proof
   reaches the `init` calls and no `False` follows. No attack found; recorded as a latent shape (see
   below).

Not tried: a Lean counterexample (no Go panic exists to build one on).

## Notes (no change to this axiom)

- The fragility of attack 6: a names-only package whose `initialize'` reaches a `FuncResolve` of
  its `init` function before any opaque step (a package with `init` functions and no translated
  variable initializers) would, under the same `∀ go.Semantics` statement, be refutable by a
  re-instantiated `functions`. The test-only `localInitFuncsOk` of
  `Dsverify/Proof/encoding/gob/InitInstancesLinked.lean` already has this shape directly
  (`{{True}} @! init.2 #() {{RET #(); True}}` for every `go.Semantics`, `functions` free at that
  name), so it is false at such an instance; it is in no statement's trust base (no statement
  imports the module), so this does not affect any result. Stating such per-function facts under
  the package's `Assumptions` (or as a premise, as `InitHyp` is in the `TopLevelRobustness`
  statements) avoids it.
- The `notes/axiom-review/README.md` index row and `notes/audit.md` row were not added (the review
  was asked not to edit existing files).

No Go bug found.
