# Axiom review: `github_com.gogo.protobuf.gogoproto.wp_initialize'` (dsverify rabia)

Reviewed 2026-11-25 by the `axiom` skill (independent reviewer), on worktree `/shared/etcd-grove-mathrand`,
branch `dsv-fix3` at `23a50393f5`; Go: `github.com/gogo/protobuf` v1.3.2 (`examples/dsverify/rabia/go.mod`),
go1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`); Perennial at `/shared/perennial-fce59af75`.

## The axiom

`Perennial.github_com.gogo.protobuf.gogoproto.wp_initialize'`
(`Dsverify/Proof/github_com/gogo/protobuf/gogoproto/Init.lean`; the class `InitHyp` there states the same):

    GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.gogoproto g →
    {{ ownInitializing g }} initialize' #() {{ RET #(); ownInitializing g ∗ isPkgInit gogoproto }}

Claims, in plain words:

1. the package's initializer (`package.init` around its 79 untranslated variable initializers,
   `fileDescriptor_592445b5231bc2b9.init`, and the two `init` functions resolved by name) returns
   without panicking;
2. it establishes the package fact, which is `True` (`Base.lean`: no variables, no model);
3. it needs no imported package initialized: the translation is names only with `imports = ["!*"]`
   (`Dsverify/Code/github_com/gogo/protobuf/gogoproto.toml`), so `pkgImportedPkgs := []` and
   `GetIsPkgInitProp` asks for nothing beyond the package's own (trivial) fact.

## Verdict: **survives** (for the rabia kit; with one stated condition on the program, below)

## The Go code

`gogoproto/gogo.pb.go` (v1.3.2): 76 `var E_X = &proto.ExtensionDesc{...}` (allocations of literals),
three `var _ = proto.Marshal / fmt.Errorf / math.Inf`, the `fileDescriptor_…` byte-slice literal, and

- `init()` (l. 708-785): 76 calls `proto.RegisterExtension(E_X)`;
- `init()` (l. 787): `proto.RegisterFile("gogo.proto", fileDescriptor_…)`.

gogo `proto` (v1.3.2): `RegisterExtension` (`proto/extensions.go:587-598`) creates the per-type map
if absent and **panics** `"proto: duplicate extension registered"` if the field number is already
registered for the extended type; `RegisterFile` (`proto/properties.go:605`) only assigns
`protoFiles[filename]`. The only panic in the initializer is therefore a duplicate extension
(field 62001-67008 on gogo's `descriptor.{File,Message,Field,Enum,EnumValue}Options`).

## Attacks tried

1. **Duplicate registration within the package.** Go test (scratch module, gogo v1.3.2,
   go1.27.3): importing `gogoproto` initializes without panic; 76 extensions registered over the five
   option types (= 76 `RegisterExtension` calls, so all field numbers distinct per type); then a
   second `RegisterExtension(gogoproto.E_Nullable)` panics
   `proto: duplicate extension registered: descriptor.FieldOptions 65001` — the panic is real, but
   only on a second registration.
2. **Duplicate registration from another package of the kit.** `go list -deps ./...` of the rabia
   module: the gogo packages linked are `proto`, `protoc-gen-gogo/descriptor` and `gogoproto`
   (plus go-redis's unrelated `internal/proto`). Grepping every dependency's sources for
   `RegisterExtension(`: only `gogoproto/gogo.pb.go` (and `proto/extensions.go`, the definition).
   `descriptor`'s inits call `RegisterType`/`RegisterEnum`/`RegisterFile` on its own names only;
   rabia's `message.pb.go` imports `gogoproto` for its side effect and registers `message.*`
   names only (`RegisterType` logs duplicates, `RegisterEnum` of `message.MsgType` is disjoint from
   anything `gogoproto` registers). The golang/protobuf registry is separate (not linked, different
   types anyway). `go test ./internal/message/` (which runs the whole init chain) passes. No
   duplicate in any of the kit's thirteen programs (all in that module).
3. **A hypothetical program that pre-registers a conflicting extension** (package `x`, initialized
   before `gogoproto`, calling `proto.RegisterExtension` with field 65001 on
   `descriptor.FieldOptions`, or writing the map `proto.RegisteredExtensions` returns): Go panics in
   `gogoproto`'s init. Not provable in Lean from the axiom: `x`'s init needs a spec of
   `proto.RegisterExtension`/`RegisteredExtensions`, which the trust base does not have (gogo
   `proto.Hyps`, `Dsverify/Proof/github_com/gogo/protobuf/proto/Spec.lean`, specs only
   `RegisterEnum` of `"message.MsgType"`, `RegisterType`, `RegisterFile`), and `x` translated names
   only would bring its own init axiom. So this is the axiom's **condition**, not a counterexample:
   it is true of programs in which no package initialized before `gogoproto` registers one of its
   extension numbers on gogo's descriptor options. Worth a sentence in the docstring if a future
   kit links another gogo-extension package (e.g. a vendored copy of `gogo.proto`), or if a
   `RegisterExtension` spec is ever added to `proto.Hyps` (it must then exclude `gogoproto`'s
   numbers, or the pair of axioms falls).
4. **Running twice / re-entry.** `initialize'` is `package.init pkg_id…gogoproto body`, which skips
   the body once `PackageInitCheck` reports the package initialized, as Go runs an initializer once.
   Re-entry while in progress needs an import cycle (impossible in Go) or the opaque body calling
   itself; no translated code reaches `package.init pkg_id…gogoproto` except through `initialize'`.
5. **Concurrency with the registry.** The real init writes `proto`'s unsynchronized maps; a racing
   registration would be a `concurrent map writes` fatal error. The axiom holds `ownInitializing g`
   (hence the exclusive `ownGoState`) across the call, and every gogo `proto.Hyps` spec requires
   `ownGoState σ`, so no proved thread can register concurrently with it; Go runs initializers
   sequentially anyway.
6. **The missing import precondition** (claim 3). Real `gogoproto` needs `proto`'s `extensionMaps`
   (`proto` initialized first, which Go always does). In the model, `message`'s
   `pkgImportedPkgs` lists `gogoproto` before `proto`, so the model initializes them in the
   opposite order from Go. Harmless: both initializers are opaque with fact `True`, no modelled state
   is shared between them, so no Lean fact depends on the order; every real program initializes
   `proto` first, where attacks 1-2 show the initializer returns.
7. **The package fact.** `True`; nothing about `E_X`'s values or `proto`'s registry is claimed, so
   no false pure fact or `↦□` can be read back.

## Not tried / framework-level remark

- No Lean counterexample (no Go panic reachable from the kit's programs to prove one for).
- Shared by every names-only initializer axiom, not specific to this one: the axiom is quantified
  over every `GooseSemantics`/`go.Semantics`, and the untranslated parts are opaque `val`s and
  `functions init.«0» []` (unconstrained by any `FuncUnfold`). It is a claim about the semantics of
  real Go; a semantics instance whose `functions` maps `gogoproto.init.0` to a panicking closure
  would contradict it, if such an instance can be built satisfying `go.Semantics` (not
  investigated; the same convention every trust-boundary axiom of an untranslated function rests on).

No Go bug found; nothing for `issues/`.

## Proposed restatement

None. Optionally add to the docstring: "true in programs where no package initialized before
`gogoproto` registers one of its extension numbers (62001-67008) on gogo's `descriptor.*Options`;
in the rabia kit only `gogoproto` calls `RegisterExtension`."
