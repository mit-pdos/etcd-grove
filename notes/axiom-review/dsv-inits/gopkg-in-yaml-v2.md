# Axiom review: `gopkg_in.yaml_v2.wp_initialize'` (dsverify quepaxa)

- **Axiom**: `Perennial.gopkg_in.yaml_v2.wp_initialize'`, `Dsverify/Proof/gopkg_in/yaml_v2/Init.lean`
  (worktree `etcd-grove-mathrand`, branch `dsv-fix3`, head `23a50393f5`); the same statement as the
  class `InitHyp`'s field `wp_init` in that file:
  ```lean
  axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
      (Hinit : GetIsPkgInitProp pkg_id.gopkg_in.yaml_v2 get_is_pkg_init) :
      {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit pkg_id.gopkg_in.yaml_v2 }}
  ```
- **Package fact** (`Dsverify/Proof/gopkg_in/yaml_v2/Base.lean`): `isPkgInit_inst :=
  define_is_pkg_init iprop(True)`, `get_isPkgInit_wf_inst := build_get_is_pkg_init_wf`. The section
  declares `[HasExt Net.netExt]`, but the instance does not use it: `#check` with `pp.explicit` of the
  axiom (a scratch file, `lake env lean`) shows `@isPkgInit_inst GF` and `get_isPkgInit_wf_inst`, the
  Base instances, so the statement is about this `True` fact. `#print axioms wp_initialize'`: Lean's
  three and the axiom itself.
- **Translation** (names and types only): `Dsverify/Code/gopkg_in/yaml_v2.lean`. `PkgInfo`'s
  `pkgImportedPkgs := []`; `initialize'` (line 1341) is `package.init yaml_v2 (λ_.
  disableLineWrapping.init; mapItemType.init; durationType.init; defaultMapType.init; ifaceType.init;
  timeType.init; ptrTimeType.init; base60float.init; default_tag_directives.init; resolveTable.init;
  resolveMap.init; yamlStyleFloat.init; allowedTimestampFormats.init; structMap.init;
  eventStrings.init; init.«0»())`, each `X.init` an `opaque` value and `init.«0»` a function name
  with no body (`«_».init` is declared, not called).
- **Go**: `gopkg.in/yaml.v2` v2.4.0 (`examples/dsverify/quepaxa/go.mod:20`), go1.27.3.
- **Users**: `Dsverify/Proof/raxos/configuration/Init.lean:57-58` (`initLb_of_spec … wp_initialize' _
  Hinit.2.1`), through it the quepaxa kit's generated `Init.lean`s (`quepaxanet`, `cmd/{server,client}*`,
  `cmd/orch`, `replica/src`); the test-only `InitInstancesLinked.lean` derives `InitHyp` from two local
  axioms (the 15 opaque initializers and `init.«0»` return), which no statement imports.
- **Verdict: survives** (2026-11-25). No counterexample; none exists (below).

## The claim in plain words

1. Run with permission to initialize (`ownInitializing g`), `initialize'` returns `#()` without panic
   and without getting stuck.
2. It gives `ownInitializing g` back and `isPkgInit yaml_v2`, which is `True` (both its deps part,
   from an empty import list, and its def part).
3. The only premise: `GetIsPkgInitProp yaml_v2 g`, i.e. `g yaml_v2 = isPkgInit yaml_v2` (no import
   constrained).

## The real initializer (v2.4.0)

Package-level variables and the one `init`:

- `apic.go:82` `disableLineWrapping = false`;
- `decode.go:238-245` `mapItemType`, `durationType`, `defaultMapType`, `timeType`, `ptrTimeType` =
  `reflect.TypeOf(<constant-typed value>)`, `ifaceType = defaultMapType.Elem()` (a map type's `Elem`:
  no panic);
- `encode.go:298` `base60float`, `resolve.go:84` `yamlStyleFloat`: `regexp.MustCompile` of constant
  patterns (panics only on a compile error; both compile, deterministic);
- `parserc.go:1007` `default_tag_directives`, `resolve.go:226` `allowedTimestampFormats`,
  `yamlh.go:243` `eventStrings`: literals; `resolve.go:17-18` `resolveTable = make([]byte, 256)`,
  `resolveMap = make(map…)`; `yaml.go:307` `structMap = make(map…)`;
- `resolve.go:20-54` `func init()`: writes `resolveTable` at indices `'+'`, `'-'`, digits, `yYnNtTfFoO~`
  and `'.'` (all `< 256`, the table has 256 entries) and fills `resolveMap` from a constant list (only
  this goroutine runs during init: no concurrent map write).

None reads input, the environment or another package's mutable state; none can panic. Checked at the
pin: a Go program importing the package (`/shared/tmp/yamlrev/go`, not kept) starts and
`yaml.Unmarshal("a: 1\nb: [x, y]\nc: .inf\n")` returns `map[a:1 b:[x true] c:+Inf] <nil>` (so the
`init` tables are in place) at go1.27.3 (and go1.27.1); every quepaxa program starts.

## Attacks tried

1. **A false package fact.** The fact is `True`, so the post claims nothing about the package's
   variables (not the regexps, not `resolveMap`'s contents, not `structMap` empty). Nothing to falsify
   by reading a variable after init; no spec of a yaml function exists in the part (yaml is names
   only, "never reached": `notes/dsv-quepaxa.md:173`; `raxos/configuration` calls `yaml.Unmarshal`,
   but no spec lets a proof step into it), so nothing gains from the init beyond `True`.
2. **A panicking initializer.** The panic paths are the two `MustCompile`s (constant valid patterns)
   and `resolveTable`'s index writes (constant indices below 256): unreachable. Claim 1 holds of Go.
3. **Missing imports in the precondition.** `GetIsPkgInitProp` constrains only `g yaml_v2`, while Go's
   initializer uses `reflect`, `regexp`, `time`, `math`. In the model `initialize'` neither initializes
   nor reads an import (`pkgImportedPkgs := []`, opaque `X.init`s), and the post names no import's fact
   or state, so an uninitialized import in the Lean context cannot turn into a false conclusion. Go
   initializes the imports first regardless.
4. **Running twice / re-entrance.** Perennial's `package.init` (`wp_package_init`,
   `Perennial/Golang/Theory/Pkg.lean:478` at `fce59af75`) returns at once when the package is recorded
   initialized, so the opaque initializers (and `init`'s writes) run at most once in the model, as in
   Go; concurrent runs are excluded by the exclusive `ownInitializing g`; an in-progress re-entry needs
   an import cycle, which Go forbids and the empty import list makes unreachable.
5. **Inconsistency.** The statement is a WP of a fixed expression built from `opaque` values and an
   unbodied function name; Lean proves nothing about their reduction, so no `⊢ False` follows (a model:
   every `X.init` `= λ_. #()` and `init.«0»` a no-op, under which the triple is provable, as the
   test-only `InitInstancesLinked.lean` does from exactly those two claims). The post's `isPkgInit` is
   `True`: no ghost resource made from nothing.
6. **Cross-world** (`crossWorld` check): no pure equation about an opaque function of a pointer; not
   applicable.
7. **Instance confusion.** Base's instance sits in a section with `[HasExt Net.netExt]` while the
   axiom's section has none; checked (above) that the axiom elaborates against Base's `True` instance,
   not some other one.

## Not tried

- The universal quantification over `GooseSemantics`/`GooseExts`/`GoGlobalContext` instances is
  common to every generated `wp_initialize'` axiom of the parts and Perennial's; not attacked here.
- No Lean counterexample attempted: no Go program panics in this initializer, so there is nothing to
  prove.
