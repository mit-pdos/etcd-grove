# Changes to Perennial this repository needs

A running list of the Perennial changes (Goose, the standard-library models and specs, the proof
framework) that proofs here are waiting on or working around. Each is a general change, designed
and reviewed on its own on a branch off Perennial's `lean` and landed by Perennial's workflow
(CLAUDE.md, "Changes to Perennial"); never a change shaped by one proof. Add an entry when a
proof hits a limitation (with the local workaround); move it to "Landed" with the Perennial commit
when the pin reaches it, and drop the workaround.

Each entry: what is missing, who needs it, the workaround here, the proposed change, status.

Started 2026-10-22 with the Kubernetes etcd3 store survey (`notes/k8s-etcd3-plan.md`, branch
`k8s-etcd3-goose`, `notes/k8s-etcd3-goose.md` there). Earlier limitations are recorded where
they were found (`notes/STATUS.md`, `notes/decisions.md`) and not yet collected here.

Perennial pin at the start: `a39a3d14c` (Perennial's `lean` head on 2026-10-22).

## Open

### Specs: `sort.Search` without monotonicity

- **Missing.** A spec of `sort.Search(n, f)` for a predicate that need not go from false to true:
  Perennial's (`Perennial/Spec/sort/Search.lean`) takes `IsMonoPred f n`; without it, the binary
  search still returns an index in `[0, n]` (its loop keeps `0 ≤ i ≤ j ≤ n`).
- **Needed by.** `authStore.RoleGrantPermission` (`server/auth/store.go`): it searches a role's
  permissions by key, and nothing records that a role record's permissions are sorted (the auth
  plan's S4d, 2026-10-24).
- **Workaround here.** `auth.wp_Search_any` (`Proof/go_etcd_io/etcd/server/v3/auth/SearchAny.lean`),
  a proof of that weaker fact over Perennial's translation of `sort.Search`.
- **Proposed change.** `sort.wp_Search_any` (or a spec whose monotonicity premise is optional)
  in Perennial's `Proof/sort`, general; then the local copy goes.
- **Status.** Open.

### Goose: a parenthesized untyped constant expression in a bitwise operation

- **Missing.** Goose translates `c | ('x' - 'X')` (`internal/strconv.lower`) as an untyped
  subtraction the semantics cannot step, whereas a lone constant (`c | 0x20`) comes out as
  `#(W8 32)`: an untyped constant expression is not folded before it meets a typed operand.
- **Met by.** Perennial's `strconv` change (`c022dbe42`, 2026-10-25): `lower` is a trusted model,
  goose's translation of `return c | 0x20`.
- **Proposed change.** Fold untyped constant expressions in goose (Go's `go/constant` gives their
  values), under Perennial's semantics-change workflow; then `lower`'s model goes.
- **Status.** Open.

### Tactics: `word`'s caches shared between parallel declarations

- **Missing.** Deterministic elaboration under a parallel build. `word`'s caches
  (`Perennial/Std/Word/Cache.lean`: `wordCache` and `failCache`, process-global `IO.Ref`s) are
  shared between the declarations Lean elaborates in parallel within one module, so whether a
  `word` call hits the cache, and hence the heartbeats a proof uses, depends on which declaration
  ran first. A proof near its heartbeat limit then fails on some runs only (and a cached failure
  could in principle leak between contexts). The same class as the flaky `stepLeader.lean` build
  (`notes/flaky-stepleader-build.md`, fixed in Perennial `fb1ecb030`, "no global mutable state
  shared between parallel declarations").
- **Needed by.** `Proof/go_etcd_io/raft/v3/raft__Step/MsgStorageAppendResp.lean`'s
  `wp_Step_MsgStorageAppendResp_snap` (D22 S-d3b): it ran out of 1000000 heartbeats once under a
  parallel full build (2026-10-21) and passes alone, on the same tree. Any proof near its limit.
- **Workaround here.** That theorem's limit raised to 4000000, with a comment citing
  `notes/STATUS.md`, "`word`'s shared cache" (what is proved is unchanged).
- **Proposed change.** The caches keyed per declaration, or held in the tactic's own state
  (`MetaM`/`TacticM` state, or an environment extension reset per declaration), so that a
  declaration's elaboration does not depend on its siblings'.
- **Status.** Not started (found 2026-10-21, `raft-retarget`, now on `lean`).

### Specs: `context.WithCancel`'s cancel function not `nil`

- **Missing.** `context.WithCancel`'s specs (`context.WithCancel.spec`, `wp_WithCancel_Background`,
  `wp_WithCancel_gen_of`, ...) return the cancel function with its triple (`cancelSpec`) but not
  that it is not `nil`, which is true (it is the closure `func() { c.cancel(true, Canceled, nil) }`,
  a `func.mk`; the proof's `simp only [recv_eq_func_mk]` sees it) and which a caller that tests the
  function against `nil` needs.
- **Needed by.** `pkg/v3/schedule`'s `fifo.Schedule` (2026-10-22, branch `fifo-sched`): it panics
  when `f.cancel == nil`, and before `Stop` `f.cancel` is the context's cancel function.
- **Workaround here.** `Proof/go_etcd_io/etcd/pkg/v3/schedule/WithCancel.lean`: local copies of
  `wp_WithCancel_gen_of` and `wp_WithCancel_Background_of` with `⌜cancel ≠ func.nil⌝` added
  (`wp_WithCancel_Background_nn`); no axiom.
- **Proposed change.** `⌜cancel ≠ func.nil⌝` in the postconditions of `WithCancel`'s specs (and of
  `WithTimeout`/`WithDeadline`'s, whose cancel functions are closures too).
- **Status.** Not started (found 2026-10-22).

### Proof idioms: a closed theorem from a program's initializer and body

- **Missing.** A form of `goose_adequacy` for the usual closed theorem: a program
  `init #() ;; body` run from a fresh state (`IsInit`) with one thread, the receipt and thread
  bounds `n + 1`, `n + 2` of an `n`-step execution, the right to initialize (`ownInitializing`)
  from the empty package state, and the conclusion with `v.isPanic = false` for each final value
  (from `UnrecoveredPanic`'s exclusion). Every closed theorem repeated these steps.
- **Needed by.** The examples' closed theorems (2026-10-22, D36): kv's, the counter's and
  kvwitness's over `goose_adequacy`; the etcd examples' over this repository's
  `goose_adequacy_start` (`Proof/runtime/Start.lean`), which stays here.
- **Workaround here.** `Proof/github_com/mit_pdos/etcd_grove/examples/common/Adequacy.lean`:
  `init_adequate` (over `goose_adequacy`, its WP obligation `progOk0`: the initializer's triple
  and the body's WP from the package's predicate and the main thread's token, at every ghost-state
  instance at the state's local context), `adequate_of_unrecovered`, `ownInitializing_of_empty`;
  no axiom. (`etcd_adequate`, the same over `goose_adequacy_start`, is this repository's.)
- **Proposed change.** `init_adequate`, `adequate_of_unrecovered` and `ownInitializing_of_empty`
  in `Perennial/GooseLang/Adequacy.lean` (or beside `IsInit` in `Perennial/Golang/Theory/Pkg.lean`).
- **Status.** Not started (2026-10-22).

### Goose: range over a function (`iter.Seq`/`iter.Seq2`)

- **Missing.** Goose rejects `for k, v := range f` when `f` is a function (`[unsupported]: range
  over func(...) (only integers, maps, slices, channels and arrays are supported)`). The iterator
  functions themselves, closures calling `yield`, already translate.
- **Needed by.** The k8s etcd3 store's `GetList` (`store.go:825`, over `pagedChunks` or
  `streamChunks`): every list. Blocks `notes/k8s-etcd3-plan.md`'s phase 5. The standard library
  increasingly returns iterators (`maps.Keys`, `slices.All`, ...).
- **Workaround here.** `store.GetList` names-only (survey branch's `etcd3.toml`); alternatives: a
  Goose fork of k8s.io/apiserver rewriting the loop, or a trusted model.
- **Proposed.** Desugar the loop as Go's compiler does: call the iterator with a closure for the
  body that returns `false` on `break`, and records a `return` (with its values) or a labelled
  `break`/`continue` in flags checked after the call; plus the runtime check that `yield` is not
  called after it returned `false` (Go panics).
- **Status.** Not started. The largest item here.

### Goose: field selection through a type alias of a struct

- **Missing.** `getStructInfo` (`goose/types.go:358`) matches `*types.Named` without
  `types.Unalias`, so a selector on a value of an alias type (`clientv3.Event = mvccpb.Event`) is
  rejected (`[impossible(go)]: expected (pointer to) struct type for base of selector`).
- **Needed by.** The k8s etcd3 watcher (`parseEvent`, `event.go:80`; `watchChan.startWatching`,
  `watcher.go:516`) and compactor (`compactor.fromWatchResponse`, `compact.go:308`). Not the
  store's unary methods.
- **Workaround here.** The three functions names-only (survey branch's `etcd3.toml`); the
  compactor configured off.
- **Proposed.** `types.Unalias` on the type and on a pointer's element in `getStructInfo`. Tried
  in a scratch copy of the pinned translator: the three translate and their `Code` and
  `GeneratedProof` elaborate; nothing else changes.
- **Status.** Not started; small. Needed before the watcher.

### Goose: imports of packages whose types a body names, and same-named packages

- **Missing.** When a body uses a method or value whose type belongs to a package the Go file
  does not import, Goose adds no import for it, and `pkgRef` (`goose/goose.go:2967`) refers to it
  through an imported package of the same name if there is one. The second is a silent
  mistranslation: `storage.InvalidError.Error` calls apimachinery's `utilerrors.Aggregate.Error`,
  emitted as the standard library's `errors.Aggregate`.
- **Needed by.** The k8s etcd3 store: `utilfeature.DefaultFeatureGate.Enabled` names
  `featuregate.FeatureGate` (`New`, `store.Delete`, nine functions in all);
  `storage.InvalidError.Error`.
- **Workaround here.** `util/feature.toml` imports `featuregate` names-only, so the name reaches
  importers; `InvalidError.Error` names-only (unreached by the store's paths).
- **Proposed.** Import the Lean module of every package whose types a translated body names, and
  make `pkgRef` an error, never a substitution, when the package is not imported under its own
  name.
- **Status.** Not started. The substitution is worth fixing first: it is wrong, not missing.

### Specs: `reflect`

- **Missing.** Perennial translates `reflect` (`Perennial/Code/reflect.lean`) but has no specs.
- **Needed by.** The k8s etcd3 store's unary methods: apimachinery's `conversion.EnforcePtr`
  (`reflect.ValueOf`, `Kind`, `Elem`) and `reflect.New(v.Type())` in `Delete` and
  `GuaranteedUpdate`; lists add `MakeSlice`, `Append` and `Value`'s methods (`growSlice`,
  `getNewItemFunc`). Plan phase 1.
- **Workaround here.** None yet; local trust-boundary specs if the Perennial change is not ready
  by phase 1.
- **Proposed.** Specs of the `reflect` subset generic code uses on pointers and slices: `ValueOf`,
  `TypeOf`, `Kind`, `Elem`, `New`, `Indirect`, `MakeSlice`, `Append`, `Len`, `Cap`, `Set`,
  `Interface`, over Perennial's model of interface values and types.
- **Status.** Not started.

### Standard library: packages not translated, and functions without specs

- **Missing translations.** `encoding/json`, `encoding/base64`, `iter`, `path` (Perennial
  translates none of them).
- **Missing specs.** `strconv.ParseInt`, `ParseUint`, `FormatInt`, `FormatUint`, `ParseBool`;
  some of `strings`; `fmt.Sprint`, `Sprintln`, `Fprintf`; `os.Getenv`; `json.Marshal`,
  `Unmarshal`; `base64.RawURLEncoding`'s methods; `path.Join`, `Clean`.
- **Needed by.** The k8s etcd3 store and `k8s.io/apiserver/pkg/storage`: continue tokens (JSON in
  base64), `prepareKey` (`path`), resource versions (`strconv`), `GetList`'s iterators (`iter`).
- **Workaround here.** The four packages names-only in this repository's configuration (survey
  branch: `Code/encoding/{json,base64}.toml`, `Code/iter.toml`, `Code/path.toml`); specs as
  needed, local until proposed.
- **Proposed.** Translations (or trusted models) of the four in Perennial's standard library, and
  the specs above, each with the subset proofs use.
- **Status.** Not started. (2026-10-22) Local trust-boundary specs here for `strings.HasSuffix`,
  `strings.Contains` (`Spec/strings/`). (2026-10-23) Also `strings.TrimSuffix` (`Spec/strings/TrimSuffix.lean`: Perennial's
  `strings` has no body for it) and `path.Join` for the one case `etcd3.New` uses
  (`Spec/path/Join.lean`: `Join(["/", p])` of a clean absolute `p` is `p`, `PathCleanAbs`).
  (2026-10-24, the auth plan's A3) The server's `UserAdd`/`UserChangePassword` call
  `base64.StdEncoding.EncodeToString`: a package *variable* of the names-only package, whose load
  needs a points-to the package's fact (`True`) does not give; they stay names only until a model
  of `encoding/base64` (and of `golang.org/x/crypto/bcrypt`'s `GenerateFromPassword`) exists.

### `reflect.Value` held in a variable: its typed points-to is `sorry`

- **Limitation.** `reflect` is names-only, and its axiomatized types' generated instances
  (`GeneratedProof/reflect.lean`: `Value_typed_pointsto`, `Value_into_val_typed`) are
  `sorry -- axiomatized type`. Any function that stores a `reflect.Value` in a variable (a
  parameter is one: Goose allocates it) needs them, so a proof of it rests on a `sorry`.
- **Needed by.** The k8s etcd3 store's `Delete` and `GuaranteedUpdate`: `v, _ :=
  conversion.EnforcePtr(out)` is passed to `conditionalDelete`, `deleteOnce`, `updateOnce`,
  `getCurrentState`, `stateFromEtcdResponse`, which make a fresh object with
  `reflect.New(v.Type()).Interface().(runtime.Object)` (`notes/k8s-etcd3-plan.md`, "What blocks
  where"). `Get` and `Create` do not use it.
- **Proposed.** An opaque `reflect.Value` with real instances (a translated struct whose fields
  are not modelled, or a hand-written typed points-to that only allows moving the value), plus
  specs of `Value.Addr`/`Type`/`Interface`/`Elem`/`Set` and `reflect.New` for pointer-to-struct
  values. Designed and reviewed on its own (Perennial's trusted base).
- **Workaround here** (the user's choice, 2026-10-22: axioms here now, a trusted model with proved
  reasoning principles later). `Proof/reflect/Values.lean`: the two instances as axioms of higher
  priority than the generated `sorry`s; opaque predicates relating a `Value` to a Go type and a
  location (`reflElem`, `reflPtr`, `reflType`) and `reflect.New`'s allocation (`reflNew`, with
  `reflNew_pointsto`); the specs of `reflect.New`, `Value.Addr`/`Type`/`Interface` and
  `conversion.EnforcePtr` as axioms (`Spec/reflect/`, `Spec/k8s_io/apimachinery/pkg/conversion/`).
  Go's `reflect` works on the runtime's representation (type descriptors, `unsafe.Pointer`,
  interfaces as two words), outside the semantics, so the model will be trusted, its principles
  proved from it.
- **Status.** Not started in Perennial.

### Goose: a names-only package's constants are values of unknown shape

- **Need.** A names-only package's constants are axiomatized `val`s
  (`k8s.io/apiserver/pkg/features.AllowUnsafeMalformedObjectDeletion`). Binding one (`let x :=
  features.F`, as Goose translates a call argument) is a beta step whose premise is that the value
  is not a panic (`pure_beta`), which nothing says of an axiom.
- **Workaround here.** `Proof/k8s_io/apiserver/pkg/features/Values.lean`: a trust-boundary axiom
  that this constant is not a panic value, used by `store.Delete`'s proof (`wp_pure` with it in
  the context).
- **Proposed fix.** Goose could translate a names-only package's constants (their values are
  constant expressions, never code), or emit with each axiomatized constant the fact that it is a
  value of its Go type (`#(c : V)` for a Lean type `V` of the constant's type), from which
  `isPanic_intoVal` gives the premise.
- **Status.** Not started.

### Goose: interface types whose methods name an alias stay axiomatized (G1)

- **Limitation.** Goose's `getStructInfo`/type translation does not see through type aliases
  (`notes/k8s-etcd3-goose.md`, G1): a type naming an alias is skipped by `translate_types`, so it
  is axiomatized. (2026-10-23) `k8s.io/apiserver/pkg/storage/feature.FeatureSupportChecker`
  (`CheckClient(ctx, client, storage.Feature)`, `storage.Feature = string`) stays axiomatized even
  with its imports configured (G4's fix made `client` concrete).
- **Needed by.** `etcd3.New` calls `feature.DefaultFeatureSupportChecker.CheckClient(...)`.
- **Workaround here.** The `storage/feature` package's fact (`checkerInit`,
  `Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean`) is the call's own WP, the variable's load
  included, so no proof touches the axiomatized type's `sorry` instances.
- **Proposed fix.** `types.Unalias` in Goose where it resolves a named type (G1).
- **Status.** Not started.

### `≤u` has no transitive instance (conversion to a defined type of a named interface)

- **Limitation.** `InterfaceSemantics.convert_to_interface` needs `to ≤u go.InterfaceType elems`;
  `≤u` (`UnderlyingEq`) is found from one `<u` step only (`unfold_to_underlying_eq`,
  `Golang/Theory/PostLifting.lean`), and `UnderlyingDirectedEq`'s docstring mentions a transitive
  instance that does not exist. A defined type of a named interface (`type Codec Serializer` in
  `k8s.io/apimachinery/pkg/runtime`: `Codec <u Serializer.ty <u interface{Encoder; Decoder}`) then
  has no conversion step.
- **Needed by.** The k8setcd3 driver's `Main` (`etcd3.New(..., codec{}, ...)`, 2026-10-23).
- **Workaround here.** A local instance proved from the two `TypeAssumptions` (`haveI` in
  `Proof/github_com/mit_pdos/etcd_grove/examples/k8setcd3/Main.lean`); no axiom.
- **Proposed fix.** An instance `[t <u t'] [t' ≤u t''] : t ≤u t''` (in place of
  `unfold_to_underlying_eq`, terminating since `<u` is directed), or the docstring corrected.
- **Status.** Not started.

### The type set of an interface with an embedded interface

- **Limitation.** `typeSetTermContains t (TypeTerm t')` is `t = t'`
  (`Golang/Defn/Interface.lean`), and Goose translates an embedded interface (`type Serializer
  interface { Encoder; Decoder }`) as `TypeElem [TypeTerm Encoder.ty]`. Go's type set of a term
  that is an interface is that interface's type set, so in the model no concrete type is in
  `Serializer`'s (or `Codec`'s) type set: a type assertion to such an interface panics where Go
  succeeds (the model is less defined, so proofs stay sound, but such an assertion cannot be
  verified).
- **Needed by.** Nothing yet (found 2026-10-23 while converting the driver's codec to
  `runtime.Codec`; conversions and method calls do not consult type sets).
- **Proposed fix.** In `typeSetTermContains`, a term whose underlying type is an interface
  contributes that interface's type set (`typeSetContains t t'`); a semantics change, through
  Perennial's `fix-semantics` workflow.
- **Status.** Not started.

### `os.Getenv`, `strconv.ParseBool` have no specs

- **Limitation.** Both are names-only in Perennial (no body, no spec).
- **Needed by.** `k8s.io/apiserver/pkg/storage/etcd3`'s `init` (`watcher.go`: whether
  `KUBE_PANIC_WATCH_DECODE_ERROR` parses as true), which the driver's initialization runs.
- **Workaround here.** Trust-boundary specs (`Spec/os/Getenv.lean`, `Spec/strconv/ParseBool.lean`,
  axioms in `Proof/`): each returns some value.
- **Proposed fix.** Specs in Perennial (`ParseBool` can be translated: it is pure).
- **Status.** Not started.

### Goose: a type defined over a type of a package the file does not import (G3)

- **Limitation.** `grpclog.LoggerV2` is `type LoggerV2 internal.LoggerV2`; `grpclog/internal` is
  not translated, so `LoggerV2` is axiomatized and a conversion to it does not step.
- **Needed by.** `etcd3`'s `init` (`logger.go`: `grpclog.SetLoggerV2(klogWrapper{})`).
- **Workaround here.** `etcd3`'s `klogWrapper_toLoggerV2` (generated into its `Init.lean` from
  `etc/gen-init.py`): the conversion returns some interface value.
- **Proposed fix.** Translate `grpclog/internal` names-only (configuration here), or G3's general
  fix in Goose (`notes/k8s-etcd3-goose.md`).
- **Status.** Not started.
- **Also `hash` (2026-10-22, branch `kvhasher`).** Perennial does not translate `hash`, so mvcc's
  `kvHasher` (a `hash.Hash32` field) was an axiomatized type with `sorry` instances, the
  repository's last two `sorry`s. Workaround here: `hash` types-only in this repository
  (`Code/hash.toml`, `-lean-root hash=`, as `encoding/hex`), which makes Goose translate
  `kvHasher` as a struct. Proposed: `hash`'s interfaces in Perennial's standard library (and
  `hash/crc32`'s model, which would make `newKVHasher`, `kvHasher.WriteKeyValue` and `Hash`
  provable); then this repository's `hash` translation goes.

### `encoding/binary`'s `Write`/`Read`, and protobuf at the bytes (2026-10-22, rafthttp stage 3, branch `rafthttp-plan`)

- **Missing.** Perennial translates `encoding/binary`'s byte orders but not `Write`/`Read`
  (names-only: they go through `reflect`); and `google.golang.org/protobuf` is names-only, so its
  `Size`/`Marshal`/`Unmarshal` have no spec there.
- **Needed by.** rafthttp's message codecs (`messageEncoder.encode`, `messageDecoder.decodeLimit`,
  the msgappv2 pair next): a length prefix written with `binary.Write` and read with `binary.Read`,
  and raft's messages marshalled.
- **Workaround here.** Trust-boundary axioms: `Spec/encoding/binary/{WriteUint64,WriteUint8,
  ReadUint64}.lean` (Go's fast path of an integer, stated over the writer's `Write` / the reader's
  `io.ReadFull`), and generic protobuf specs over a per-type wire model (D38a:
  `Proof/google_golang_org/protobuf/proto/InvProto.lean`'s `PbType`, `Spec/google_golang_org/
  protobuf/proto/{Size,Marshal,Unmarshal}Pb.lean`).
- **Proposed.** Specs of `binary.Write`/`Read` of fixed-size integers in Perennial (or a trusted
  model of their fast path); and, if the generic vocabulary proves itself across the codecs and
  the older per-type specs move onto it, `PbType` and its three specs as Perennial's protobuf
  boundary.
- **Status.** Not started.

### The `WaitGroup` join idiom's `Add(n)`, and `Sprintf` of a `Stringer` (2026-10-23, rafthttp stage 4d, branch `rafthttp-plan`)

- **Missing.** (1) `sync.join.WaitGroup.wp_Add_of` (and `sync.tokJoin`'s) covers `Add(1)` only,
  though `sync.WaitGroup.Add.spec` takes any delta. (2) `fmt.wp_Sprintf` admits arguments of
  predeclared basic types only (`fmt.ArgsWf`): an argument with a `String` method (a
  `types.ID`) is outside it, though Go's formatting then only calls that method.
- **Needed by.** (1) rafthttp's `pipeline.start`, `p.wg.Add(connPerPipeline)` (`4`). (2) rafthttp's
  `peerStatus.deactivate`, `Sprintf("failed to %s %s on %s (%s)", action, s.id, source, reason)`.
- **Workaround here.** (1) `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/
  WaitGroupAdd.lean`, `wgJoin_wp_Add4_of` (`wp_Add_of`'s proof with four ghost steps; proved, no
  trust). (2) `Spec/fmt/SprintfID.lean`, a trust-boundary axiom for `types.ID` arguments (as
  `SprintfNamed`, `SprintfClientPtr`).
- **Proposed.** (1) `wp_Add_of` for a delta `n` (`0 < n`, the bound `num_added + n < 2^31`),
  giving `n` `ownDone`s (a `[∗list]` over `List.replicate n`); the `Add(1)` statement derived.
  (2) `wp_Sprintf` over arguments whose `String`/`Error` method has a given spec (a WP returning
  some string), covering `Stringer`s generally.
- **Status.** Not started.

### `fmt.Errorf`'s result: a fresh pointer error (2026-10-23, rafthttp stage 4e, branch `rafthttp-plan`)

- **Missing.** `fmt.Errorf.spec` gives only that the error's `Error()` returns some string; it does
  not say the error is a fresh pointer (`*fmt.wrapError` or `*errors.errorString`: `IsPointerError`,
  as `errors.New.spec` says), so a caller cannot show it differs from a package's error variable.
- **Needed by.** rafthttp's `checkPostResponse`, whose `fmt.Errorf` errors must not be
  `errMemberRemoved` (`postErr`: `pipeline.post`'s caller reports only that one on `errorc`).
- **Workaround here.** None yet: `checkPostResponse` is a spec only. (Stage 5e-3) The stream
  reader's `dial` uses a local trust-boundary spec, `Spec/fmt/ErrorfPlain.lean`: with no `%w` the
  error is an `*errors.errorString` (Go's `Errorf` returns `errors.New(s)`), whose `Error()`
  returns the message, so a leaf of an error tree (`errors.Is` of it, in `run`).
- **Proposed.** `fmt.Errorf.spec`'s postcondition with `IsPointerError err` (for a format without
  `%w`), as `errors.New`'s; or the `*errors.errorString` form above.
- **Status.** Not started.

### `strings.TrimSuffix` without a spec (2026-10-23, rafthttp stage 5e-3, branch `rafthttp-plan`)

- **Missing.** Perennial translates `strings.TrimSuffix` names-only and has no spec for it
  (`TrimPrefix` has one).
- **Needed by.** rafthttp's `streamReader.dial` (a `412`'s body, `TrimSuffix(string(b), "\n")`).
- **Workaround here.** `Spec/strings/TrimSuffix.lean`, a trust-boundary axiom: some string.
- **Proposed.** A translation or model of `TrimSuffix` with a spec (the string without the suffix,
  if it ends with it), as `TrimPrefix`'s.
- **Status.** Not started.
### Tactics: framing up to the projections of a structure instance

- **Missing.** The proof mode's matching of a hypothesis against a goal (`iframe`, the `$$`
  arguments of `iapply`/`ihave`) does not see through the projection of an anonymous constructor:
  `dghostVar (γ.withPhys p).rst dq v` does not frame `dghostVar γ.rst dq v`, nor `crevFrozen γ`
  the premise `crevFrozen (γ.withPhys p)`, though they are definitionally equal (`rfl`) and Lean's
  `exact` accepts them.
- **Needed by.** The store's names at the current physical names (`mvcc.StoreNames.withPhys`,
  D22 receiver epochs S5b, 2026-10-22): every proof that works at `γ.withPhys p` and uses a
  logical fact of `γ`.
- **Workaround.** Explicit rewrites by `rfl` lemmas (`mvcc.isStore_withPhys`, ..., the
  `withPhys_simp` tactic of `InvStore.lean`), lemmas bridged in term mode
  (`readerPool_checkout_p`, `revMuInv_open_cur`), and `revMuBody` with separate logical and
  physical names.
- **Proposed.** iris-lean's (not Perennial's) frame and specialization matching could unify up to
  `whnfR` of projections of constructor applications (structure eta), as Lean's `isDefEq` does at
  reducible transparency for `instances`. Not proposed yet: to be weighed against the cost of
  every match.
- **Status.** Open (observed; no change drafted).

### Context: `Canceled`'s message cell in `context`'s package facts

- **Missing.** Perennial's context initialization allocates `Canceled` with `errors.New("context
  canceled")` and persists the `errorString`'s `s` field, but `isInit`'s `"#HCanceled"` keeps only
  `isTypedErr`: a proof cannot tell `Canceled` apart from another `errors.New` value (D37, D19k).
- **Needed by.** `ctxErrClientAllW_of` (`client/v3/ErrorsNewOk.lean`): a context's error is no
  caller's `errors.New` value (`errCellOk`), for the Kubernetes driver's sentinel errors.
- **Workaround here.** `context.ErrAny` (this repository's trust-boundary axiom) states the cell
  of `Canceled`'s value and that `DeadlineExceeded`'s is no `*errorString` (true of Go).
- **Proposed change.** `"#HCanceled"` with the cell (`x.[errorString, "s"] ↦□ "context
  canceled"`, as this repository's `errStrCell`), and `"#HDeadlineExceeded"` with its dynamic type
  (`deadlineExceededError`); then `ErrAny` drops the two facts.
- **Status.** Not started (found 2026-10-23).

## Landed

### Translation: `strconv.ParseUint`, `time.Ticker` and `Time.After`

- **Was missing.** Perennial translated nothing of `strconv` and none of `time.NewTicker`,
  `Ticker.Stop`, `Time.After`.
- **Needed by.** etcd's simple token provider (`server/auth/simple_token.go`):
  `isValidSimpleToken` parses a token's raft index with `strconv.ParseUint`; the TTL keeper's `run`
  ticks with a `time.Ticker` and compares with `Time.After`.
- **Landed.** Perennial `13a60f492` (2026-10-24, branch `time-ticker`: `NewTicker`, `Ticker.Stop`,
  `Ticker.Reset` trusted models, a ticker's channel a bag of arbitrary times; `Time.After`
  translated, returning some `bool`) and `c022dbe42` (2026-10-25, branch `strconv-parse`:
  `strconv.ParseUint` for bases 2 to 36, over the pure model `internal.strconv.parseUint`; three
  trusted models: `stringslite.Clone`, `internal/strconv.lower`, six constant tables' no-op
  initializers). The pin moved to `24bef275e` (the auth plan's S5c); `strconv`'s initializer is
  Perennial's (raft's local `strconv.opaqueInitsOk` axiom gone), and `isValidSimpleToken` is proved
  (`tokenSimple_isValid`). Left: `FormatUint`, `Itoa`, `ParseInt`, `FormatInt`, base 0.

### Specs: `sort.SearchStrings`, `sort.Strings`

- **Was missing.** A spec of `sort.SearchStrings(a, x)` (the least index whose string is not below
  `x`, on a sorted slice) and of `sort.Strings` (Perennial translated `sort.Search` and the pdqsort,
  not these two wrappers).
- **Needed by.** `auth.hasRootRole` (`sort.SearchStrings(u.Roles, rootRole)`), the root-role
  shortcut of every permission check and of `IsAdminPermitted`; `UserGrantRole` (`sort.Strings`).
- **Landed.** Perennial `beb785eaf` (2026-10-24, branch `sort-strings`): both translated and proved
  (`sort.wp_SearchStrings` over `ListSorted go.GoStringLe`, `sort.wp_Strings` a sorted
  permutation), `cmp.Less` at `string`. The pin moved to it (the auth plan's S4b), `hasRootRole`
  is translated and proved (`Proof/go_etcd_io/etcd/server/v3/auth/hasRootRole.lean`), and S3's
  axiom is gone. `UserGrantRole` still is not proved: it appends to the message `UnsafeGetUser`
  returned, which the read contract gives read-only (`notes/decisions.md`, "S4b of the auth plan").

### Specs: `context.WithTimeout`/`WithDeadline` of `Background()`

- **Missing.** A spec of `context.WithTimeout(parent, d)` (and `WithDeadline`,
  `WithDeadlineCause`) whose parent is `context.Background()` (or `TODO()`): Perennial's
  `context.WithTimeout.spec` takes `isContext parent`, which `Background()`'s value is not (its
  `Done()` is `nil`). `WithCancel` has the counterpart (`wp_WithCancel_Background`,
  `WithCancelGen.lean`), and the pieces of the deadline case are there too (`wp_background_Deadline`,
  `wp_propagateCancel_background`, `isContext_timerCtx_of`).
- **Needed by.** The pattern of client/v3's documentation, `ctx, cancel :=
  context.WithTimeout(context.Background(), timeout)` around each call: the examples' call sites
  since 2026-10-23 (`notes/client-timeouts-plan.md`, D-T2, D-T3) and the server's read loop
  (`sendReadIndex`, the request path's unit 4a).
- **Workaround here.** The trust-boundary axiom `context.WithTimeoutBackground.wp_proof`
  (`Spec/context/WithTimeoutBackground.lean`: an `isContext` of some descriptor and a callable
  `cancel`), in the `read`, `server` and every etcd example's collection; the examples use it
  through `client.wp_WithTimeout_bg` (`Proof/go_etcd_io/etcd/client/v3/TimeoutCtx.lean`).
- **Proposed change.** `wp_WithTimeout_Background` and `wp_WithDeadline_Background` (the
  `Background()` parent of `WithDeadlineCause`'s proof, as `wp_WithCancel_Background` is of
  `WithCancel`'s), with the descriptor they give (`Deadline := some d`, `PDone := True`, fresh
  Done names). Then the axiom here becomes a theorem (one axiom fewer in the baseline and in
  those collections: the plan's T3).
- **Status.** Landed: Perennial `c25bef57e` (branch `with-timeout-background` off `lean`
  `d761e15b2`, 2026-10-23: `wp_WithDeadlineCause_Background_of`, `wp_WithDeadline_Background_of`,
  `wp_WithTimeout_Background_of` in `Proof/context/WithDeadlineBackground.lean`, exposed in
  `Results.lean`; `propagateCancel`'s spec takes any child for a `Background()` parent,
  `wp_propagateCancel_background_any`); the pin moved to it and the axiom here is the theorem
  `context.WithTimeoutBackground.wp_proof` over `wp_WithTimeout_Background` (one axiom fewer in
  the baseline and in the `read`, `server` and every etcd example's collection).

### Std, PostLifting: generic lemmas the client, the cache and the examples each proved a copy of

- **Missing.** Facts about Perennial's and Lean's own definitions, proved in several places here
  (`notes/dedup-plan.md`, C1-C4 and D): a points-to at `q` as two halves and back, with agreement
  (twelve copies by value type: `ptsto_w64_halves`, `loc_halves`, `chan_split`, ...), half a
  points-to fractional (`half_pointsto_fractional_loc`/`_chan`); `N.@x` disjoint from `N.@y` and
  `N.@z` (the `*_mask` lemmas); setting the first entry of a `replicate` padding (five copies);
  one more function of a `foldl (fun o g => g o)` (`opFold_take_succ`, `stmOptsFold_take_succ`,
  `cfgApply_take_succ`); indexing and prefix facts Lean core lacks (`zip_get_snd`,
  `getElem?_snoc_cases`, `prefix_drop_cons`, the `crl_*_mid` three, `flatten_getElem?`, ...);
  `GoStringLt` on cons cells (`client/v3/PrefixRange.lean`).
- **Needed by.** `Proof/go_etcd_io/etcd/{client,cache}/v3/`, `examples/{linkvtxn,lintest}`.
- **Workaround here.** None now (the local copies stayed until the pin moved).
- **Proposed change.** Perennial branch `dedup-lemmas` (`f97c83add`, off the pin `537c426e0`;
  worktree `/shared/perennial-dd`): `typedPointsto_half_split`/`_half_combine`/`_half_fractional`
  (`Golang/Theory/PostLifting.lean`), `mask_ndot_ne2` (`Std/Namespaces.lean`), the list lemmas
  (`Std/List.lean`, sections `list_index`, `subslice_take`, `join_same_len_index`),
  `goStringLt_cons_iff`/`_nil_cons`/`_not_nil` (`Golang/Defn/String.lean`). Theorems only.
  Then, here: each copy deleted and its uses pointed at Perennial's (the `_take_succ` three stay
  one-liners over `foldl_apply_take_succ`: `opFold` and its kin are in specs' statements).
- **Status.** Landed 2026-10-22: Perennial `lean` `f97c83add`, the pin since; the local copies are
  deleted (etcd-grove branch `dedup-pin`), their uses pointed at Perennial's (the server's
  `mask_ndot_ne2` at `nroot` and the three `_take_succ` one-liners over Perennial's; raft's
  `ptsto_halves` too). Found 2026-10-22.

### Proof idioms: a synchronous SPSC channel, a thread-token join, a ghost update at a fork

Three of the watch client's local workarounds (D25, `notes/decisions.md`, "S1c's findings" and
"R4's findings"; `notes/status-history.md`, "watch-resume"), proposed as general idioms.

- **Missing.** (1) Perennial's SPSC idiom (`Idioms/Spsc.lean`) does not tie its pending channel
  states to the sides' tokens, so the holder of both tokens of an unbuffered channel cannot show
  that nothing is in flight (Go's synchronous handoff). (2) Its `WaitGroup` join idiom
  (`sync.join`) bounds the `Add`s since the last `Wait` (`num_added < 2^31 - 1`), not the
  goroutines running. (3) `wp_fork_tok`'s premise is a plain wand: no ghost update (no invariant
  opened) at the fork step, which is not atomic (`Fork` may stutter).
- **Needed by.** The watch client's reconnection: `respc` and every substream's `recvc` (`run`'s
  epoch switch and a substream's restart need `sent = recv`); `waitCancelSubstreams`' local wait
  group (one `Add(1)` per resuming substream, F4); its goroutines' inner `go` statement, which
  refills a lent slot at the fork.
- **Workaround here (until the pin moves).** `Proof/go_etcd_io/etcd/client/v3/SyncSpsc.lean` (a
  copy of `Spsc.lean` with pending flags); `InvWcJoin.lean`'s local join (`wcjAdder`, `wcjDone`,
  `wcjDoneB`, `wp_wcj_Add`/`Done`/`Wait`) and its copy of `wp_fork_tok`, `wp_fork_tok_upd`.
- **Proposed change.** Perennial branch `idioms` (off `lean` `a39a3d14c`), one commit each:
  `3c3e83e2c` `Idioms/SyncSpsc.lean` (`isSspsc`, `sspscProducer`/`sspscConsumer`, `sspsc_sync`,
  the `recvAu`/`sendAu`/`closeAu` lemmas and `wp_sspsc_receive`/`send`/`close`); `9e52da638`
  `wp_fork_tok_upd` in `GooseLang/Lifting.lean` (`wp_fork_tok` derived from it, statement
  unchanged); `537c426e0` `Proof/sync/WaitGroupTokJoin.lean`, `sync.tokJoin` (`ownAdder`,
  `ownDone`, `WaitGroup.wp_Add`/`wp_Done`/`wp_Wait`, the counter backed by thread tokens; a slot's
  token lendable, `lend_acc`/`unlend_acc`, under a client's lending law `lendLaw N L`). New
  definitions and theorems only; no existing statement changes. Reviewed (`trusted-delta.py`: no
  tier 0-2 trust change), recorded with `etc/land.sh mark-reviewed`.
- **Status.** Landed 2026-10-22: Perennial `lean` `537c426e0` (`3c3e83e2c`, `9e52da638`,
  `537c426e0`), the pin since; the local copies are deleted (etcd-grove branch `perennial-idioms`).

### Small gaps met by rafthttp's stream writer (stage 5b, 2026-10-23)

- **Missing.** (1) A typed points-to's halves: `typedPointsto l v (own 1) ⊣⊢ half ∗ half` is
  proved only in an example (`goose/testdata/examples/channel/etcd_session/Base.lean`,
  `pointsto_halves`), not the library. (2) `len(ch)` of a channel: `wp_auto` does not unfold
  `functions go.len [chan]` (`FuncUnfold`'s `len_chan`) to `Channel.Len`, so `chan.wp_Len` applies
  only after `wp_func_call; wp_call`. (3) `make([]T, n)` of a large concrete `n` (rafthttp's 1 MiB
  `msgAppV2BufSize`): `wp_slice_make2`'s postcondition names `List.replicate n zero`, which the kernel
  unfolds when a proof frames it (a deterministic timeout); a spec with the contents abstracted
  (`∃ zs, sl ↦* zs ∗ ⌜zs.length = n⌝`) avoids it.
- **Needed by.** `streamWriter.close` (the writer's fields split between its goroutine and its
  lock), `streamWriter.closeUnlocked` (`len(cw.msgc)`), `newMsgAppV2Encoder` (its buffer).
- **Workaround here.** `rafthttp/Writer.lean`'s `typedPointsto_halves` and
  `typedPointsto_combine_halves`; `wp_func_call; wp_call` before `wp_Len`;
  `newMsgAppV2Encoder.lean`'s `wp_make_bytes_abs`.
- **Proposed change.** (1) The halves lemma in `Golang/Theory/PostLifting.lean`; (2) `len_chan`'s
  unfolding in `wp_auto`'s simp set; (3) `wp_slice_make2_abs`/`make3_abs` beside the existing specs.
  Not yet proposed.
- (2026-10-23, rafthttp stage 5c) **A non-blocking send on a bag channel** (`select` with a
  `default`): the bag idiom (`Idioms/Bag.lean`) has the blocking send only. Workaround:
  `rafthttp/Reader.lean`'s `bag_nonblocking_send_au` (`bag_send_au` without the waiting case).
  Proposed change: the lemma beside `bag_send_au`. Not yet proposed.
- (2026-10-24, rafthttp stage 6d) **`wp_apply` aborts silently inside a `wp_join` case**: in
  `raftNode.start`'s loop, `wp_apply HSend $$ [...]` of the transport's `Send` (an interface method,
  its spec a hypothesis whose precondition now holds the loop's `E.S`) throws "unknown free
  variable" (visible with `+noauto`) and, without `+noauto`, an abort that leaves the case's goal
  admitted with no error: the module builds with a `sorry` only `#print axioms` and
  `etc/tcb-report.py` see. Workaround here: `wp_bind` the call and `iapply` the hypothesis
  (`raftNode__start.lean`). Proposed change: find the escaping free variable (probably the case's
  generalized context) and make `wp_apply` report it as an error. Not yet proposed.
- (2026-10-24, rafthttp stage 6f) **An axiomatized type's `sorry` instances shadow its `TypeRepr`**:
  for a type Goose cannot translate (`net/http`'s `Request`, `Response`) the generated proof has
  `X_typed_pointsto`/`X_into_val_typed` as `sorry -- axiomatized type`, and instance search takes
  `TypeRepr X.underlying X` from them (`IntoValTyped.type_repr`) although the translation's
  `X.TypeAssumptions.type_repr` gives it: a field reference (`StructFieldRef`, `req.Header`)
  then reaches the `sorry` (`etc/tcb-report.py`), with no load or store of the whole value.
  Workaround here: `Proof/net/http/Boundary.lean`'s `Request_typeRepr`,
  `Request_underlying_typeRepr` (and `Response`'s), high-priority instances from the type
  assumptions. Proposed change: Goose emits no `IntoValTyped` instance for an axiomatized type
  (or one of low priority), so its `TypeRepr` comes from the type assumptions. Not yet proposed.
### `wp_apply`'s frame list can admit a goal silently

- **Missing.** In `mvcc.restoreChunk.wp_proof` (2026-10-23), `wp_apply (wp_spsc_send …) $$
  [$Hsp $Hprod HP]` followed by a bullet for `HP`'s subgoal elaborated with no error, but the
  rest of the enclosing bullet never ran and the theorem got a `sorryAx` (found only through
  "declaration uses `sorry`", located by printing the `sorryAx` terms' source names). Framing a
  prepared hypothesis (`$HP'`) instead proved it.
- **A second instance** (2026-10-23, `schema.authBackend.GetUser.wp_proof`, the auth plan's S1):
  `wp_apply (hRU l rt R Held D) $$ [$Htxf $Hrtx $HD] as HR` at the *deferred* `tx.RUnlock()` call
  (the goal `WP ((RUnlock #() ;; oldf #()) ;; #u) {{Φ}}` after `wp_with_defer`'s body returned),
  `hRU` a Lean spec whose instance names `D`, a variable introduced after the defer by an earlier
  `wp_apply ... as ⟨%D, ...⟩`: no error at the line, the rest of the proof runs on nothing, and the
  theorem ends with "unsolved goals" showing the goal as it was before the call. `wp_apply_core`
  of the same term fails with "unknown free variable" (`_fvar...`), while `have h := hRU l rt R
  Held D` elaborates, and `wp_apply` of the same shape worked for `hRL` two calls earlier (before
  `D` existed). Workaround: `wp_bind` the call, then `iapply (hRU ...) $$ [Hpkg Htxf Hrtx HD]`,
  prove the precondition goal by `iframe`, `inext`, `iintro HR`.
- **Workaround here.** Prepare the hypothesis with `ihave` and frame it with `$`; check every new
  proof for the "declaration uses `sorry`" warning; at a deferred call, `wp_bind` and `iapply`.
- **Proposed change.** Not designed: a minimal reproduction first, then make the tactic report
  the error instead of admitting.

### Std, String: the successor string and the order's facts

- **Missing.** Lemmas about `GoStringLt`/`GoStringLe` beyond the four in
  `Perennial/Golang/Theory/String.lean`: that `k ++ "\x00"` is the immediate successor of `k`
  (`GoStringLt k b → k ++ "\x00" = b ∨ GoStringLt (k ++ "\x00") b`, so `k < b ↔ k ++ "\x00" ≤ b`
  and `k < key ++ "\x00" ↔ k ≤ key`), that a string is below its proper extensions, that `""` is
  the least string, and `GoStringLe`'s transitivity/antisymmetry/totality.
- **Needed by.** etcd's point interval `[k, k ++ "\x00")` (the watchable store's watchers on a
  key, the auth store's point permissions and `checkKeyPoint`): `mvcc/InvWatchGroup.lean`
  (`strLt_succ_le`, `succ_ne_empty`, `ivlCmp_point_iff`), `adt/Contains.lean` (the same three,
  restated so that `auth` does not import `mvcc`), `auth/PermTree.lean` (`goStringLt_succ_iff`),
  `adt/Model.lean` (`strLt_append`), the B-tree's and the cache's `goStringLe_*`.
- **Workaround here.** The copies above.
- **Proposed change.** The lemmas in `Perennial/Golang/Theory/String.lean`, with `GoStringLe`'s
  order instance; the copies here then go.

### Sequential specs of an `RWMutex` no one else can reach

- **Missing.** Perennial's `RWMutex` specs need the lock allocated (`isRWMutex`/`ownRWMutex`,
  `init_RWMutex`); code that locks a mutex of an object not yet shared (etcd's `restoreIntoIndex`
  on the index it is rebuilding, `restore` on `s.revMu` inside `NewStore`) has no spec.
- **Workaround here.** `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/PlainRWMutex.lean`:
  `plain.wp_RLock`/`wp_RUnlock`/`wp_Lock`/`wp_Unlock` on owned memory (values `rwZero`, `rwR1`,
  `rwW`), and `plain.wp_Mutex_Lock`/`wp_Mutex_Unlock` for the trusted spin lock, proved over
  Perennial's translation (no assumption).
- **Proposed change.** The same lemmas in Perennial's `Proof/sync` (for `Mutex` and `RWMutex`),
  stated for any number of nested readers if needed; not yet designed.

### `wp_apply` of a hypothesis fails as "unsolved goals" at the proof's `by`

- **Missing.** In `mvcc.store.restore.wp_proof` (2026-10-23), `wp_apply Hru $$ [$Htok]` (an
  Iris hypothesis, the read transaction's `RUnlock` triple from `keyReadLocked`) failed with
  "unsolved goals" reported at the theorem's `:= by`, the goal shown being the call, and the
  tactics after it never ran (a `fail` after it did not fire). The same call is applied this way
  in `storeTxnRead__End.lean`.
- **Workaround here.** `wp_bind` the call, then `iapply Hru $$ [Htok]`, `iexact Htok`, `inext`,
  `iintro`.
- **Proposed change.** Not designed: a minimal reproduction first; the tactic should report
  where and why it fails.
