# Axiom review: `google_golang_org.grpc.wp_initialize'` (dsverify quepaxa)

- **Axiom**: `Perennial.google_golang_org.grpc.wp_initialize'`,
  `Dsverify/Proof/google_golang_org/grpc/Init.lean` (worktree `etcd-grove-mathrand`, branch `dsv-fix3`,
  head `23a50393f5`); the same statement as the class `InitHyp` in that file:
  ```lean
  axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
      (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc get_is_pkg_init) :
      {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
      {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit pkg_id.google_golang_org.grpc }}
  ```
  Package fact (`Base.lean`): `define_is_pkg_init iprop(True)`, so `isPkgInit grpc` is
  `□ isPkgInit context ∗ True`; `GetIsPkgInitProp grpc g` is `g grpc = isPkgInit grpc ∧
  GetIsPkgInitProp context g` (`build_get_is_pkg_init_wf`).
- **Translation** (names and types only, the part's own): `Dsverify/Code/google_golang_org/grpc.lean`,
  translated from the **model** `models/grpc` (`etc/dsv/quepaxa.py`: `module_models`), not from
  grpc-go. `PkgInfo.pkgImportedPkgs := [context]`; `initialize'` (l. 1661) is `package.init grpc (λ_.
  context.initialize'; DefaultBackoffConfig.init; …; modelChooseRandom.init; …; «_».init ×6;
  FuncResolve init.«0»/«1»/«2» ())`: 44 opaque `X.init` values and three `functions init.<k> []`
  that the package's `Assumptions` do not constrain (no `FuncUnfold`).
- **Go**: what runs is grpc-go v1.84.0 (`examples/dsverify/quepaxa/go.mod`, no `replace`; the model
  only in a `models/grpc/gomodel.py` build), go1.27.3, with its 111 non-standard transitive imports
  (x/net, x/text, x/sys, protobuf-go v1.36.12, genproto, grpc's internal packages).
- **Users**: `Dsverify/Proof/raxos/replica/src/Init.lean:114` (`initLb_of_spec … grpc.wp_initialize'`);
  the test-only derivation `InitInstancesLinked.lean` (local axioms `localOpaqueInitsOk`,
  `localInitFuncsOk`). HYP_IMPORTS: quepaxa sets none, so `'all'`: the precondition constrains
  `context`, the only package the model's `initialize'` reaches (as `etc/dsv/README.md` requires).
- **Verdict: refuted in Go, Lean counterexample not built** (2026-11-25). A Go program that registers
  a protobuf file or name that a package in grpc's untranslated import closure also registers panics
  during grpc's initialization (protobuf-go's registry conflict), while the axiom (together with the
  no-op `TrustedCode` models of protoc-gen-go initializers) lets Lean prove its initialization does
  not panic. The quepaxa kit's own programs are **not** affected: they register no conflicting
  name and start (checked below). Every other attack failed.

## The claim in plain words

1. From `ownInitializing g` (with `g grpc` and `g context` the canonical facts), `initialize'`
   returns `#()`: no panic, not stuck, **whatever the rest of the program has done before** (the
   precondition says nothing about any other state).
2. It returns `ownInitializing g` and `isPkgInit grpc` (`isPkgInit context`, plus `True`).

The docstring's argument: "Go runs them at program start and they return (the kits' programs
start)": evidence about the kit's programs, while the statement is about every program.

## The real initializer

grpc's own package (v1.84.0): five `func init()` (`clientconn.go:777`, `service_config.go:166,328`,
`server.go:72`, `dialoptions.go:46`) assigning `internal.*` hooks and `emptyServiceConfig`; the only
panic is `clientconn.go:780` on parsing the constant `"{}"` (unreachable). Variable initializers:
errors, `status.Error` values, option defaults, the logger. The model (`models/grpc`) has three
`init`s (`dialoptions.go:45`, `rpc_util.go:45`, `server.go:75`) and, among its variables,
`modelChooseRandom = os.Getenv("GRPC_MODEL_CHOOSE") == "random"`: no panic path.

Before grpc's own package, Go initializes its 111 non-standard imports. Their initializers read the
environment (`internal/envconfig`: ~40 `GRPC_*` variables; `grpclog`: `GRPC_GO_LOG_*`;
`internal/binarylog`: `GRPC_BINARY_LOG_FILTER`; x/net `http2`: `GODEBUG`,
`DEBUG_HTTP2_GOROUTINES`; protobuf `GOPROTODEBUG`) and **register protobuf descriptors in
protobuf-go's global registry** (`grpc/binarylog/grpc_binarylog_v1`, `genproto/googleapis/rpc/status`,
`types/known/{anypb,durationpb,timestamppb}`). `protoregistry.(*Files).RegisterFile` panics on a
file path or full name already registered (`reflect/protoregistry/registry.go:47-65`,
`conflictPolicy = "panic"`, overridable only by `GOLANG_PROTOBUF_REGISTRATION_CONFLICT=warn|ignore`).
In the model, none of these packages exists: their initialization is folded into the opaque steps
of the one `initialize'` that represents grpc, i.e. into this axiom.

## Attacks tried

1. **A false package fact.** The fact is `True` (and `isPkgInit context`, which the model's
   `initialize'` establishes itself by calling `context.initialize'`, and which Perennial proves). No
   variable value is claimed: nothing to falsify by reading after init. The specs that take
   `isPkgInit grpc` (`Dsverify/Proof/raxos/Hyp.lean:389-463`, `NewServer`, `Dial`, …) are hypotheses of
   their own and gain only `True` from it. **Fails.**
2. **A panicking initializer, environment-driven.** A Go program importing real grpc
   (`grpc.NewServer()` in `main`) run with every one of the 30 environment variables above set at once
   to each of 30 adversarial values (`''`, `x`, `-1`, `99999999999999999999999`, `18446744073709551615`,
   `json`, `fatal`, `all`, `none`, `grpc.method=true,,=,`, `*{h:99999999999999999999}`, `-a/b{1}`,
   `http2debug=2`, `nolazy`, `bogus`, …), and `GRPC_BINARY_LOG_FILTER` alone at 13 malformed filters:
   0 failures of 43 runs (parsers fall back to defaults; `NewLoggerFromConfigString` warns and
   returns nil). The model build (`gomodel.py`), with `GRPC_MODEL_CHOOSE` in `'' random x true`: no
   failure. **Fails.**
3. **A panicking initializer, state-driven (protobuf registry conflict).** **Succeeds in Go.**
   Program (`google-golang-org-grpc/main.go.txt`, `go.mod.txt`): module `aaa`, package `aaa/dup` a
   verbatim copy of `grpc/binarylog/grpc_binarylog_v1/binarylog.pb.go` (package clause renamed);
   `main` imports `_ "aaa/dup"` and `grpc`. Go 1.21+ initializes, among the packages whose imports
   are done, the first by import path, so `aaa/dup` (needing only protobuf's runtime) registers
   `grpc/binlog/v1/binarylog.proto` before `grpc_binarylog_v1`, whose `init.0` (`binarylog.pb.go:977`)
   then panics (`google-golang-org-grpc/run.log`, exit 2, every run):
   ```
   panic: proto: file "grpc/binlog/v1/binarylog.proto" is already registered
   	previously from: "aaa/dup"
   	currently from:  "google.golang.org/grpc/binarylog/grpc_binarylog_v1"
   ```
   The same with the model build (`gomodel.py`: the model keeps `internal/binarylog`). The package
   chosen is imported by grpc only (via `internal/binarylog`), not by `grpc/codes` or `grpc/status`,
   so in the model the panic can be represented only by grpc's `initialize'`; with
   `GOLANG_PROTOBUF_REGISTRATION_CONFLICT=warn` it starts.
   *In Lean*, the program's initialization would be: `aaa/dup` translated like `raxos/proto` (its
   descriptor-table initializers and `init.0` trusted models that do nothing, e.g.
   `Dsverify/TrustedCode/raxos/proto/client.lean:27-41`), then `grpc.wp_initialize'`. Both steps are
   given; nothing in either precondition mentions the registry, so main's `wp_initialize'` (no panic)
   follows by the generated init walk. **Not built**: it needs a new goose project, its translation
   and generated `Init`/`PkgTable` in the `Dsverify/` part, which this review was not to add (no edits
   to `etc/goose.py`, no builds). Expected cost: small (the walk is what `etc/gen-init.py` generates);
   the risk is only plumbing. Which statement is false: the no-op model of `aaa/dup` is true of
   `aaa/dup`'s own init (it registers first and returns); the claim that fails is this axiom's claim
   1 in a state the precondition does not exclude. Equally, if the duplicate's path sorted after
   `google.golang.org/…`, the panic would be in the duplicate's own init and the no-op `TrustedCode`
   model would be the false claim: the two trusted pieces together omit the registry.
4. **Missing imports in the precondition.** `GetIsPkgInitProp` constrains `context` only, which is
   exactly what the model's `initialize'` initializes, so the `ownInitializing` table never needs a
   fact it lacks (`etc/dsv/README.md`'s `HYP_IMPORTS` rule holds). Go's other imports run their
   initializers before grpc, but the post names no fact of theirs: no false conclusion follows from
   their absence (beyond attack 3, which is about their effects, not their facts). **Fails.**
5. **Running twice / re-entrance.** `package.init` (`wp_package_init`, Perennial
   `Golang/Theory/Pkg.lean:352`) returns at once when grpc is recorded initialized, and the post's
   `isPkgInit grpc` then comes from the table; concurrent runs need two `ownInitializing`. Go has no
   import cycles; in the model grpc imports only `context`. **Fails.**
6. **Inconsistency.** The opaque `X.init` values are fixed constants Lean cannot reduce (a model: every
   `X.init = λ_. #()`). The three `functions init.<k> []`, however, are fields of the
   `GoSemanticsFunctions` instance the axiom quantifies over, unconstrained by `Assumptions`: in a
   semantics where `functions grpc.init.0 [] = λ_. panic`, the triple is false. Deriving `False` in
   Lean would need a concrete `go.Semantics` instance and an adequacy run; not attempted. This is the
   repository's convention for every names-only function axiom (the main tree's
   `Proof/google_golang_org/grpc/Init.lean:61-67`, `initFuncsOk`; `MustRegister.wp_proof`): the reading
   is "in the semantics of the real code". Noted, not counted against this axiom.
7. **Cross-world.** No pure equation about an opaque function of a pointer; not applicable.

## The kit's programs

Every quepaxa program imports grpc; their `.pb.go` files (`raxos/proto`, `raxos/proto/client`) register
`proto/…` files of their own package `raxos`/`client`, no name of grpc's closure. A real
`examples/quepaxanet/cmd/server1` built at the pin passes initialization (ran 3 s, killed by
`timeout`, no panic). So the kit's results do not rest on a false instance of the axiom; the gap is in
the statement's generality, which the docstring justifies only by "the kits' programs start".

## Proposed restatement (not applied)

1. Short term: make the justification checkable, not universal: a gate that builds every program
   whose initialization applies a names-only `wp_initialize'` (the `PROGRAMS` of the kits) and runs
   its package initialization (e.g. `go test -run '^$'` of a test file in the program's package, or the
   binary with a flag that exits in `main`), unset `GOLANG_PROTOBUF_REGISTRATION_CONFLICT`; and say
   in the docstring that the axiom is sound only for programs that pass it (a program's package set
   decides it, not grpc).
2. Principled: model protobuf-go's registry as ghost state (the set of registered file paths and full
   names): the protoc-gen-go initializer models register their names (and require them absent),
   and a names-only package's `wp_initialize'` requires the names its untranslated closure registers
   to be absent and adds them. The same applies to every names-only init axiom whose closure has
   generated protobuf code (the main tree's grpc, `grpc/status`, genproto, etcd's api packages) and to
   the `TrustedCode` descriptor-initializer models.

## Not tried

- The Lean counterexample (attack 3), for the reasons given there.
- Registry conflicts by full name from a different file path (same mechanism, `registry.go`'s name
  check), and conflicts with `anypb`/`durationpb`/genproto `status` (attributed in the model to
  `grpc/status`'s or protobuf's initializer rather than grpc's).
- Other global registries grpc's closure writes (`encoding.RegisterCodec`, `balancer.Register`,
  `resolver.Register`): they overwrite, no panic path found by reading, not tested.

Index: `notes/axiom-review/README.md` and `notes/audit.md` were not edited (review brief); this
report needs their rows.
