# Axiom review: `github_com.rs.zerolog.wp_initialize'` (dsverify rabia)

- **Axiom**: `Perennial.github_com.rs.zerolog.wp_initialize'`,
  `Dsverify/Proof/github_com/rs/zerolog/Init.lean` (worktree `etcd-grove-mathrand`, branch `dsv-fix3`,
  head `23a50393f5`); the same statement as the class `InitHyp` in that file:
  ```lean
  axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
      (Hinit : GetIsPkgInitProp pkg_id.github_com.rs.zerolog get_is_pkg_init) :
      {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit pkg_id.github_com.rs.zerolog }}
  ```
  The package fact (`Dsverify/Proof/github_com/rs/zerolog/Base.lean`): `define_is_pkg_init
  iprop(True)`, so `isPkgInit zerolog` is `□ isPkgInit io ∗ □ True` (`isPkgInitDeps` from
  `pkgImportedPkgs`); `GetIsPkgInitProp zerolog g` is `g zerolog = isPkgInit zerolog` plus `io`'s
  (and its imports') well-formedness (`build_get_is_pkg_init_wf`).
- **Translation** (names and types only): `Dsverify/Code/github_com/rs/zerolog.lean`. `PkgInfo`'s
  `pkgImportedPkgs := [pkg_id.io]` (Go's import list is much longer: `bytes`, `context`,
  `encoding/json`, `fmt`, `io/ioutil`, `os`, `strconv`, `sync`, `sync/atomic`, `time`,
  `internal/json`, ...); `initialize'` is `package.init zerolog (λ_. 34 opaque X.init calls;
  init.0; init.1)`, each `X.init` an `opaque` value, `init.«0»`/`init.«1»` names with no body.
- **Go**: `github.com/rs/zerolog` v1.23.0 (`examples/dsverify/rabia/go.mod:22`), go1.27.3.
- **Users**: rabia's generated `Init.lean`s (`Dsverify/Proof/rabia/internal/logger`,
  `roles/server`, `roles/server/layers/{proxy,consensus}`), through `EtcdGrove.initLb_of_spec … 
  ExternalInit.github_com_rs_zerolog wp_initialize'`; `HYP_INITS` in `etc/dsv/rabia.py:62`. Test-only
  derivation from local axioms: `InitInstancesLinked.lean` (walks `initialize'` over
  `localOpaqueInitsOk`/`localInitFuncsOk` and Perennial's proved `io.wp_initialize'`).
- **Verdict: survives** (2026-11-25). No counterexample; none found.

## The claim in plain words

1. Run with permission to initialize (`ownInitializing g`), zerolog's `initialize'` returns `#()`
   without panic and without getting stuck.
2. It gives `ownInitializing g` back and `isPkgInit zerolog`, whose content is `io`'s package fact
   and `True`: nothing about zerolog's own variables.
3. The only premise: `g` agrees on `zerolog` and on `io` (and `io`'s imports).

## The real initializer (v1.23.0)

Package-level initializers (default build; `binary_log` swaps `encoder_json.go` for
`encoder_cbor.go`, same shape):

- `globals.go:23-96`: string literals (`TimestampFieldName = "time"`, the `Level*Value`s, ...),
  `CallerSkipFrameCount = 2`, function literals (`LevelFieldMarshalFunc`, `CallerMarshalFunc`,
  `ErrorMarshalFunc`), `InterfaceMarshalFunc = json.Marshal`, `TimeFieldFormat = time.RFC3339`,
  `TimestampFunc = time.Now`, `DurationFieldUnit = time.Millisecond`, `DurationFieldInteger = false`;
  `globals.go:100-101`: `gLevel`, `disableSampling = new(int32)`;
- `array.go:9`, `event.go:12`, `console.go:32`: `sync.Pool` literals (their `New` closures not run);
- `context.go:328`: `th = timestampHook{}`; `context.go:393`: `ch = newCallerHook(...)` (a struct);
- `encoder_json.go:13-15`: `_ encoder = (*json.Encoder)(nil)`, `enc = json.Encoder{}`;
- `sampler.go:11-15`: `Often/Sometimes/Rarely = RandomSampler(n)` (a `uint32` conversion);
- `init.0` (`ctx.go:9`): `SetGlobalLevel(TraceLevel)` (an atomic store to `*gLevel`, initialized
  before any `init` by Go's order), `disabledLogger = &Nop()` (`New(nil)`: `ioutil.Discard`, no
  panic path);
- `init.1` (`encoder_json.go:18`): assigns a closure to `internal/json.JSONMarshalFunc`
  (zerolog's own internal package; `internal/json/string.go:9`'s `init` fills a table).

None reads input or the environment; none writes another package's state outside zerolog's own
`internal/json`; none can panic (no indexing, assertion, division or nil dereference on these paths).
Checked at the pin: a program importing zerolog v1.23.0 (go1.27.3, default build and
`-tags binary_log`) starts, sees `GlobalLevel() == TraceLevel` and `TimeFieldFormat ==
time.RFC3339` after init, `ParseLevel("warn") == 2`, logs a filtered `Info` and a `Warn`, and
`Ctx(context.Background())` returns the `disabledLogger` (level `disabled`). Output:
`{"level":"warn","k":"v","message":"shown"}` / `ok disabled`. Every rabia program starts.

## Attacks tried

1. **A false package fact.** zerolog's own part is `True`: the post claims nothing about any of its
   variables (not `gLevel`, not the `Level*Value` strings, not the pools). Nothing to falsify by
   reading a variable after init. Its dependency part is `isPkgInit io`: Go initializes `io` before
   zerolog (it imports it: `log.go:103`) and no zerolog initializer assigns an `io` variable (grep
   of `io.X =` over the package and `internal/json`: none), so `io`'s fact still holds after it.
2. **A panicking initializer.** None (above); claim 1 holds of Go. In the model the order of the
   `X.init`s and `init.0`/`init.1` is the translator's; whatever it is, the claim is about the opaque
   values, which stand for Go's initializers, which Go runs in its own valid order.
3. **Missing imports in the precondition.** `GetIsPkgInitProp` constrains only `zerolog` and `io`,
   while Go's initializers touch `encoding/json` (`json.Marshal`), `time` (`time.Now`,
   `time.RFC3339`), `sync`, `sync/atomic`, `io/ioutil` (`Discard`) and `internal/json`. In the model
   `initialize'` initializes only `io` and names no other import's fact or state in its post, so an
   uninitialized import in the Lean context yields no conclusion about it. Go initializes them first
   regardless.
4. **Running twice / re-entrance.** Perennial's `package.init` returns at once when the package is
   recorded initialized (`wp_package_init`, `Perennial/Golang/Theory/Pkg.lean`, at `fce59af75`); the
   post holds either way. Concurrent runs are excluded by the exclusive `ownInitializing g`. Go runs
   `init` once and there are no import cycles.
5. **Interaction with `zerolog.Hyps`** (`Spec.lean`, out of scope otherwise). The specs need only
   `isPkgInit zerolog`, which this axiom grants with no ownership of zerolog's globals. Two specs
   depend on mutable globals the fact does not pin: `ParseLevel("warn") = WarnLevel` compares with
   `LevelFieldMarshalFunc(WarnLevel)`, i.e. `LevelWarnValue` (`log.go:160-181`), and the level
   methods read `gLevel`. A Go program that assigns `zerolog.LevelWarnValue` or
   `zerolog.LevelFieldMarshalFunc` makes `ParseLevel("warn")` fail. This is not reachable in Lean:
   the fact `True` gives no points-to for any zerolog global, so no proof can write one (and rabia's
   Go code assigns none: grep of `zerolog.X =` over `examples/dsverify/rabia`). Worth a sentence in
   `Hyps`'s docstring ("true while the program does not reassign zerolog's exported variables"), not
   a defect of this axiom.
6. **Inconsistency.** A WP of a fixed expression built from `opaque` values; Lean can prove nothing
   about their reduction, so no `⊢ False` follows (a model: every `X.init` and `init.N` `= λ_. #()`,
   under which the triple is the test-only walk of `InitInstancesLinked.lean`). The post creates no
   ghost resource beyond `io`'s fact, which Perennial's proved `io.wp_initialize'` establishes.
7. **Cross-world** (`crossWorld` check): no pure equation about an opaque function of a pointer; not
   applicable.

## Not tried

- The universal quantification over `GooseSemantics`/`GooseExts`/`GoGlobalContext` instances is
  common to every names-only `wp_initialize'` axiom (mit-pdos/etcd-grove#8), not specific to zerolog.
- No Lean counterexample attempted: no Go program panics, so there is nothing to prove.
