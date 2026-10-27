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

### Tooling: incremental proof checks, and long `·` blocks as auxiliary theorems

- **Missing.** A way to check a proof after an edit without elaborating the whole file
  (`lake build` and `lake env lean` start over each time; Perennial's tutorial checks a file
  with `lake build`), and a way to keep the once-per-declaration work of a long Iris proof
  (instantiation, sharing, the kernel's check of one huge term) from being redone on every edit.
- **Needed by.** Every proof here and in Perennial; most for the longest
  (`watchGRPCStream.run`, 3368 lines: an edit near its end costs about its fresh time).
- **Workaround here.** `etc/lean-check.py` (a kept Lean server; `--fast`, `-e`, `--goal`,
  `--split`) and `Proof/AbstractBullets.lean` (option `abstractBullets`), both generic: the
  script names no project, the tactic module nothing of this repository's.
- **Proposed change.** Move both to Perennial (`etc/lean-check.py`, the tactic in its
  `PerennialMeta` library), document the loop in `docs/PERENNIAL_PROOF_TUTORIAL.md` beside
  `lake build`; `lean-check.py` here then imports nothing of its own (`SPLIT_MODULE`).
- **Status.** Open (2026-10-26, `notes/STATUS.md`, "Checking proofs while editing them").

### Specs: `(*Time).After`

- **Missing.** The pointer-receiver form of `time.Time.After` (Perennial's `Proof/time/PtrMethods.lean`
  has `Add`, `Before`, `Sub` only).
- **Needed by.** etcd's TTL keeper (`simpleTokenTTLKeeper.run`: `nowtime.After(tokenendtime)` on an
  addressable `Time`; the auth plan's S5e, 2026-10-25).
- **Workaround here.** `auth/TokenKeeperRun.lean`'s `time_wp_ptr_After`, the shape of
  `Time.wp_ptr_Before_of`.
- **Proposed change.** `Time.wp_ptr_After_of`/`Time.wp_ptr_After` beside `Before`'s.
- **Status.** Open.

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
- **Also the watch cache (2026-10-26, branch `kep-6404`, `notes/kep-6404-plan.md`).** The cacher's
  `processEvent`, `UpdateResourceVersion` and `waitUntilFreshLocked` use the cacher's `metrics`
  variables, of component-base's `metrics` types (`CounterVec`, `HistogramVec`), which the cacher
  does not import: the substitution names them `cacher.metrics.CounterVec` (`Unknown identifier`).
  Workaround here: `cacher.toml` drops its import of the cacher's `metrics` (both are then named
  by their paths) and the names arrive through `consistency`'s public import of the cacher's
  `metrics` and its of component-base's (names only). Its cost: `watchCacheEvent`, whose
  `timeline` field is a `metrics.DispatchTimeline`, is axiomatized (`translate_types` skips a type
  naming a package not imported), so `processEvent` and `UpdateResourceVersion`, which build one,
  cannot be proved until the general fix.
- **Also the DaemonSet controller (2026-10-27, branch `k8s-daemonset-proof`; gap D2 of
  `notes/k8s-daemonset-goose.md`).** Kubernetes names nearly every API and client package `v1`, so
  the substitution hits the controller's main path: `syncDaemonSet` (component-base's
  `metrics.CounterMetric` named as the controller's `daemon/metrics`), `RealPodControl.createPods`
  and `DeletePod` (client-go's typed `PodInterface` named as `k8s.io/api/apps/v1`'s), `ComputeHash`
  (the standard library's `hash.Hash32` as `pkg/util/hash`'s), the node-affinity `Match`es
  (metav1's `ObjectMeta` as core/v1's); ten functions names only. **Tried**: `pkgRef` returning the
  package's own path always (the substitution loop deleted) in a scratch copy of the pinned
  translator: all ten translate and their modules elaborate (the interfaces' modules are in scope
  through public imports), and no other file of the project changes. Now the most needed of the
  open Goose changes for the DaemonSet proof.

### Specs: the builtin `max` (2026-10-26, branch `kep-6404`)

- **Missing.** No spec of the predeclared `max` (`functions go.max [t, t]`): each proof proves its
  own: raft's `wp_max2_uint64` (`raft/v3/InvTracker.lean`), mvcc's `sw_wp_max_int64`
  (`watchableStore__syncWatchers.lean`), the watch cache store's `wp_max_uint64` (`cacher/store/
  DefsWCS.lean`).
- **Proposed.** A spec of `max`/`min` on the integer types in Perennial's predeclared theory.
- **Status.** Not started.

### Goose: a constraint interface's `comparable` term (2026-10-26, branch `kep-6404`)

- **Missing.** `translate_types` accepts an interface that embeds `comparable`
  (client-go's `tools/cache.Object`: `interface { GetName() string; GetNamespace() string;
  comparable }`) and emits `go.type_term.TypeTerm go.comparable`, which Perennial does not define
  (`Unknown identifier go.comparable`).
- **Needed by.** Nothing yet: the watch cache's store names `tools/cache`'s indexer types only;
  (2026-10-26) the local half of `tools/cache` (store, thread-safe map, indexers) does not use
  `Object`; the typed informers (`TypedResourceEventHandler[T Object]`, DaemonSet plan phase 4) will.
- **Workaround here.** `client_go/tools/cache.toml` without `translate_types`: the types it
  translates are listed by name (2026-10-26, `notes/k8s-clientgo-goose.md`, C6), `Object` stays
  axiomatized.
- **Proposed.** Either a `go.comparable` type set in Perennial's semantics, or Goose rejecting
  (axiomatizing) such an interface under `translate_types`, as it does other unsupported types.
- **Status.** Not started.

### Goose: a promoted method of a generic struct, through a pointer (2026-10-26, client-go survey C2)

- **Missing.** For a generic struct `S[T]` with an embedded field, the pointer receiver's unfolding
  of a promoted method (`ptr_M_unfold` in `S.TypeAssumptions`, `goose/lean_types.go:338`) names the
  struct as `ctx.glangType(t.Obj(), t)`, the generic type without its type argument
  (`StructFieldRef delayingType.ty ...`, ill-typed); the value receiver's case uses `ty`.
- **Needed by.** client-go's workqueue (`delayingType[T]`, `rateLimitingType[T]`,
  `TypedBucketRateLimiter[T]`): every call through `TypedRateLimitingInterface[T]` (the DaemonSet
  controller's `Get`, `Done`, `AddRateLimited`) resolves through these unfolds.
- **Workaround here.** The promoted methods excluded in `Code/k8s_io/client_go/util/workqueue.toml`
  (no `MethodUnfold` for them); their specs are hypotheses of the work queue's results that reach
  them (2026-10-27, `notes/k8s-clientgo-goose.md`, "What C2 leaves unlinked").
- **Proposed.** `glang.VerbatimExpr(ty)` for the struct there (one line; tried in a scratch copy of
  the pinned translator: workqueue's translation then elaborates, nothing else changes), with a
  Goose test of a generic struct embedding an interface.
- **Status.** Not started.

### Goose: an axiomatized type alias is declared under another name than its uses (2026-10-26, client-go survey C3)

- **Missing.** An axiomatized alias is declared `axiom X : go.GoType` (`goose/types.go:65`) but
  referred to as `X.ty` like every type.
- **Needed by.** client-go's workqueue (`klog.Logger = logr.Logger` in its configs).
- **Workaround here.** klog's config imports `github.com/go-logr/logr` (names only), so the alias
  translates.
- **Proposed.** Declare the axiomatized alias as `X.ty`.
- **Status.** Not started.

### Goose: `min`/`max` of a named integer type (2026-10-26, client-go survey C4)

- **Missing.** `min(a, b)` on `time.Duration` is rejected (`comparison between non-assignable
  types`): `goose.go:926` joins the first parameter's underlying type with the others' types.
- **Needed by.** client-go's `flowcontrol.Backoff.Next` and `tools/cache`'s
  `threadSafeMap.Transaction` (names only here).
- **Workaround here.** The two names only.
- **Proposed.** Emit `go.min` at the parameters' (named) type and let its semantics take the
  underlying type (type choices are the Lean semantics', Perennial's `AGENTS.md`); joining the
  underlying types in Goose also works (tried in a scratch copy: both translate and elaborate) but
  makes that choice in Goose.
- **Status.** Not started.

### Goose: a struct field named like a type of its package (2026-10-26, client-go survey C5)

- **Missing.** In `S.TypeAssumptions` (in `S`'s namespace), a field type that is a package type of
  the same name as a field (`intstr.IntOrString`'s field `Type` of type `Type`) resolves to the
  field's projection (`(y : Type')` is `IntOrString.Type'`).
- **Needed by.** `k8s.io/apimachinery/pkg/util/intstr.IntOrString` (the DaemonSet's rolling-update
  fields).
- **Workaround here.** `intstr`'s structs axiomatized (`translate_types_except_structs`).
- **Proposed.** Qualify package-level types in the generated lemmas (`_root_.Perennial.<pkg>.T'`).
- **Status.** Not started.

### Goose: range over a string (2026-10-26, client-go survey C1)

- **Missing.** `for i := range s` over a string (`[unsupported]: range over string`).
- **Needed by.** apimachinery's `resourceversion.isWellFormed` (the consistency store's
  comparisons).
- **Workaround here.** `isWellFormed` names only (a trust-boundary spec, or a trusted model as the
  byte loop, which computes the same result).
- **Proposed.** Range over a string, stepping by `utf8` decoding (needs a model of
  `utf8.DecodeRuneInString`).
- **Status.** Not started.

### Goose: a deferred call drops its variadic argument (2026-10-27, client-go workqueue)

- **Missing.** `deferStmt` (`goose/goose.go:2128`) calls the deferred function `$f` with
  `$a0 .. $a(n-1)` for the call's `n` syntactic arguments, but `callExprPrelude` binds the
  arguments as the callee's parameters: for a variadic callee, the variadic slice is one more name
  (`$a1`, `slice.nil` when no variadic argument is passed). So `defer
  utilruntime.HandleCrashWithLogger(logger)` (`HandleCrashWithLogger(logger, handlers ...)`)
  becomes `$f $a0`, a partial application: the deferred function never runs. (With variadic
  arguments passed, presumably the converse: more names applied than bound.)
- **Soundness.** The model is not Go's: a deferred variadic call does nothing in it, so a proof says
  nothing about that call's effects (a trust-base bug, not a missing feature).
- **Needed by.** client-go's workqueue: `delayingType.waitingLoop` (`defer
  utilruntime.HandleCrashWithLogger(logger)`) and `Typed.updateUnfinishedWorkLoop`
  (`HandleCrashWithContext`).
- **Workaround here.** None: `delayingType.waitingLoop`'s proof leaves its two returns (where the
  deferred call runs) `sorry` (gap G-defer-variadic) rather than prove the model's no-op.
- **Proposed.** In `deferStmt`, apply `$f` to the names the prelude binds (the callee signature's
  parameter count for a variadic call); a Goose test of `defer f(x)` with `f(x int, ys ...int)`.
- **Status.** Not started.

### Tactics: `wp_apply` after an atomic spec applied with `iapply` (2026-10-27, client-go consistency)

- **Missing.** In a proof that applies a logically atomic spec (the `<<{ … }>>` triples of
  `Perennial/ProgramLogic/AtomicFupd.lean`) with `wp_bind; iapply spec $$ [...]`, a later
  `wp_apply lem $$ [...]` in the continuation (after the atomic update is closed) silently does
  nothing: no error at the tactic, the declaration reports only "unsolved goals" at its `by`, and
  `wp_apply_core` there fails with "unknown free variable" and "declaration has metavariables".
  Seen in `Proof/k8s_io/client_go/util/consistency/consistencyStore__WroteAt.lean` (the call of
  `ownerRecord.WroteAt` after `ensureWrittenRecord`'s atomic spec). `wp_apply` directly on the
  atomic spec has the same symptom.
- **Workaround here.** `wp_bind; iapply lem $$ [...]` for the later call too, then `inext; iintro`
  its postcondition.
- **Proposed.** Find the metavariable `wp_apply` leaves (probably the continuation `Φ` of the
  atomic spec, instantiated late, whose context then loses a local cleared by `wp_auto`), and make
  `wp_apply` support atomic specs directly.
- **Status.** Not started.

### Specs: `fmt`'s `ArgWf` for a method-less map argument (2026-10-27, client-go informers)

- **Missing.** Perennial's `fmt.Errorf` spec requires each argument well formed (`ArgWf`), which
  has no case for a value of a named map type without a `String`/`Error` method (`sets.Set[string]`,
  printed with `%v`). client-go's `AddIndexers` passes two.
- **Workaround here.** `Proof/k8s_io/client_go/tools/cache/ErrorfSet.lean` proves
  `wp_Errorf_setArgs` from the model with the faithfulness of that case as its premise.
- **Proposed.** An `ArgWf` case for maps whose type has no formatting method (the value printed
  structurally; the spec needs only that `Errorf` returns a non-nil error).
- **Status.** Not started.

### Tactics: `wp_load` misses a field of a whole-struct points-to with a generic-struct field (2026-10-27, client-go listers)

- **Missing.** With `s ↦{dq} (⟨ri⟩ : daemonSetLister)` in context (a struct whose one field is the
  generic `listers.ResourceIndexer[T]`), `wp_load` of `s.[daemonSetLister, "ResourceIndexer"]`
  reports "could not find a points-to in context covering the address", although the generated
  `AccessStrict` instance `daemonSetLister_access_load_ResourceIndexer` exists and applies when
  used by hand.
- **Workaround here.** Specs state the field points-to (`s.[daemonSetLister, "ResourceIndexer"] ↦
  ri`); constructors split the allocation with the instance's `access_strict`
  (`Proof/k8s_io/client_go/listers/apps/v1/NewDaemonSetLister.lean`).
- **Status.** Not investigated.

### Tactics: `iframe` leaves persistent hypotheses unframed after `iapply` of an atomic spec (2026-10-27, client-go listers)

- **Missing.** After `iapply (atomicSpec ...) $$ [Hr] HAU`, the precondition goal
  `isPkgInit ∗ isCache … ∗ typedOK …` (all available as `□` hypotheses) is not closed by `iframe`;
  `isplitr; iexact H` per conjunct is needed. Similarly after `wp_apply (wp_Pop …) $$ [Hpop Hdn]`
  for `isFIFO`/`processOk` in `controller__processLoop.lean`.
- **Status.** Not investigated.

### Semantics: `sync.Mutex{}` (2026-10-26, client-go workqueue)

- **Missing.** `sync.Mutex`'s model has underlying type `go.bool` (`TrustedCode/sync.lean`), and a
  composite literal at a named type steps at its underlying type, so `&sync.Mutex{}` reaches
  `CompositeLiteral go.bool (LiteralValueV [])`, which has no step (composite literals step at
  structs, arrays, slices, maps and pointers only).
- **Needed by.** client-go's `newQueue` (`sync.NewCond(&sync.Mutex{})`); the backend's
  `backend.wp_mutexLit` (`storage/backend/MutexLit.lean`) states the same gap as an axiom.
- **Workaround here.** A hypothesis class, `EtcdGrove.MutexLitSemantics`
  (`Proof/sync/MutexLitSemantics.lean`, in `SEM_PREMISES`): the empty literal of `go.bool` is
  `false`.
- **Proposed.** An empty composite literal of a type whose underlying type is not a struct (and
  has no literal rule) is its zero value; or `sync.Mutex`'s model as a struct.
- **Status.** Not started.

### Semantics: `float64(c)` of an untyped integer constant (2026-10-27, client-go workqueue)

- **Missing.** `backoff > math.MaxInt64` with `backoff : float64` is emitted as `Convert
  go.untypedInt go.float64 #c` at run time, and `UntypedIntSemantics` converts untyped integers to
  the integer types only.
- **Needed by.** client-go's `TypedItemExponentialFailureRateLimiter.When`.
- **Workaround here.** A hypothesis class, `EtcdGrove.UntypedIntToFloat64Semantics`
  (`Proof/k8s_io/client_go/util/workqueue/UntypedIntToFloat.lean`, in `SEM_PREMISES`): it steps to
  an uninterpreted float of the integer, as `float64(n)` of a typed integer does.
- **Proposed.** Goose folding the constant conversion, or the step in `UntypedIntSemantics`.
- **Status.** Not started.

### Specs: `container/heap` (2026-10-27, client-go workqueue)

- **Missing.** No specs of `container/heap` in Perennial. This repository states `heap.Push`,
  `heap.Fix` (the lessor's), `heap.Init`, `heap.Pop` (the work queue's) as trust-boundary axioms
  over the contract `heap.heapIface` (`Proof/container/heap/Defs.lean`); `Init` and `Pop` are
  stated up to a permutation (no heap order).
- **Proposed.** Proved specs in Perennial (the package is plain Go over `heap.Interface`).
- **Status.** Not started.

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
- **Missing specs.** (2026-10-26) client-go's leaf libraries add `sync.WaitGroup.Go`,
  `container/heap.Init`/`Pop`, `math.Pow`, `os.LookupEnv`, `time.Time.Add/Before/Sub`,
  `math/rand.New`/`Rand.Float64` (the full list per package: `notes/k8s-clientgo-goose.md`).
  Earlier: `strconv.ParseInt`, `ParseUint`, `FormatInt`, `FormatUint`, `ParseBool`;
  some of `strings`; `fmt.Sprint`, `Sprintln`, `Fprintf`; `os.Getenv`; `json.Marshal`,
  `Unmarshal`; `base64.RawURLEncoding`'s methods; `path.Join`, `Clean`. (2026-10-24, rafthttp stage 7d)
  `io.MultiReader` (names-only: an axiom here, `Proof/io/MultiReader.lean`, stated over the
  snapshot pipe's `readerStreams`); `bytes.Buffer`'s methods (a struct without method bodies: the
  k8s-etcd3 axioms `ownBuffer_new` and `Buffer.Write`, which the snapshot sender also uses). (2026-10-25,
  rafthttp stage 7e) `fmt.Sprintf` of non-basic arguments (`fmt.SprintfArgs`, over `fmt.argsOk`, as
  `Printf`/`Errorf`: Perennial's `wp_Sprintf` takes basic types only); `(*time.Duration).String`
  (`time` is translated without `Duration.String`, so its pointer wrapper is missing too).
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

### `os.Getenv`, `strconv.ParseBool`, `strconv.ParseInt` have no specs

- **Limitation.** All three are names-only in Perennial (no body, no spec).
- **Needed by.** `k8s.io/apiserver/pkg/storage/etcd3`'s `init` (`watcher.go`: whether
  `KUBE_PANIC_WATCH_DECODE_ERROR` parses as true), which the driver's initialization runs.
  (2026-10-27, branch `k8s-leaf-cache`) `ParseInt`: client-go's thread-safe store
  (`tools/cache`, `parseRVForMetricsWithTruncation`, the resource-version metric).
- **Workaround here.** Trust-boundary specs (`Spec/os/Getenv.lean`, `Spec/strconv/ParseBool.lean`,
  `Spec/strconv/ParseInt.lean`, axioms in `Proof/`): each returns some value.
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

### `encoding/base64` (the auth plan's E2u, 2026-10-26)

- **Missing.** Perennial has no `encoding/base64`, not even names-only, so etcd's
  `EtcdServer.UserAdd` and `UserChangePassword` (they hash the password with bcrypt and put the
  hash in the request base64-encoded, `v3_server.go`) cannot be translated here.
- **Workaround here.** The apply side names the encoding as an opaque function
  (`auth.stdB64Enc`, `auth/Requests.lean`) and `selectPassword`'s boundary spec says its decoding
  of an encoding has no error; that the handler's request is of that form (`UserAddModel.pwSure`)
  is a proposer's obligation (`commitOkOn`, E2t) until the handler is proved.
- **Proposed change.** `encoding/base64` in Perennial: `StdEncoding` (a package variable with its
  fact), `EncodeToString` and `DecodeString` with a model of the standard encoding (or at least
  `DecodeString (EncodeToString b) = (b, nil)`), translated or as trusted models.

### An interface embedding interfaces is an exact type set (2026-10-27, DaemonSet plan phase 3, gap C8)

- **Missing (at the pin).** Goose writes an interface that embeds interfaces with the embedded
  ones as type terms (`TypeElem [TypeTerm Object.ty]`), and `typeSetContains` reads a type term
  as that exact type: an assertion of a concrete type to such an interface panics in the
  semantics where Go's succeeds. The model API server's `copyObject`
  (`o.DeepCopyObject().(object)`, `object` embedding `runtime.Object` and `metav1.Object`) is a
  `sorry` (`notes/k8s-apimodel-goose.md`).
- **Status.** Fixed on Perennial's `lean` after the pin (`8ef540a62`, `d30f71f36`: an interface
  written as all its methods, method sets emitted); here with the pin bump.

### `wp_load` of a struct field through a fractional points-to (2026-10-27, DaemonSet plan phase 3)

- **Missing.** Loading a field (`![t] (StructFieldRef T f l)`) needs `l`'s struct points-to at
  fraction 1 for `wp_auto` to split it; at a fraction `dq` (a persistent configuration, a shared
  `*Preconditions`) the load is stuck.
- **Workaround here.** Persistent structs are stated field by field (the model's `cfgAt`); a
  fractional one is split by `iStructNamed` and recombined with `typedPointsto_combine` around the
  loads (`Server.remove`'s preconditions, the `ObjectMeta` accessors).
- **Proposed change.** The field-access instance (`solve_pointsto_access_struct`) at any fraction.

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

### An `RWMutex`'s reader slots are leaked by readers that hold them for life

- **Missing** (2026-10-26, D22 J0). `RWMutex.RLock` takes a reader token (`ownRLockToken`), of which
  a lock has `actualMaxReaders` (`2^30 - 1`, `ownRWMutex`'s `Hmax`). A goroutine or an object that
  takes a token for its whole life and is then abandoned (not joined) leaks it in the proof, while
  in Go only the readers inside `RLock`..`RUnlock` at one time count. etcd's server repeats this
  once per received snapshot: `applySnapshot`'s `RemoveAllPeers` stops each peer without joining
  its two `Process` goroutines (`peer.go:173-205`, `:314-333`), which hold a slot of the server's
  `lgMu` each (`startPeer.lean`'s `HR7`/`HR8`), and the new `UberApplier` takes a slot of the auth
  store's `enabledMu` that the old one never gives back. So any finite stock runs out after enough
  snapshots, and an unbounded number of snapshots cannot be verified.
- **Needed by.** D22's second-snapshot loop (`notes/snapshot-sj-plan.md`, "J0 decisions", gap 5;
  stages J8b and L3).
- **Workaround here.** None that is free. Until the change lands, J8a states `srvSnapApplied` with
  the slots it can return and the stock threaded from `NewServer` (`NewServer` drops the rest of
  `NewAuthStore`'s `actualMaxReaders` slots and `lgMu`'s today: J1b keeps them), and J8b closes the
  loop only if the stock suffices; the fallback is a named premise bounding the snapshots a member
  applies in a run, for the user's approval.
- **Proposed change.** `RLock` paid by a thread token (`GooseLang/Threads.lean`) when
  `threadBound ≤ actualMaxReaders`: every reader is a live thread, so the readers at one time are
  bounded by the threads, which is the real reason Go's counter does not overflow. A reader token
  then need not be held between critical sections. Not yet designed; general (any program whose
  goroutines read-lock a long-lived `RWMutex`), not shaped by this proof.
- **Landed** (2026-10-26, Perennial `3c64ae292`, branch `rlock-thread-token`): `Perennial/Proof/ThreadPool.lean`
  (`threadPool.isThreadPool N γ R`: at least `threadBound - 1` copies of `R`, a thread token swapped for
  a copy, `borrow`/`borrow_lc`/`giveBack`) and `Perennial/Proof/sync/RWMutexThreads.lean`
  (`init_RWMutex_threadPool`: every reader token in a pool, premise `threadBound GF ≤ 2^30`). Additive,
  no trusted-base change. Limitation: one thread token borrows one copy at a time, so a thread holding
  two thread-paid read locks at once pays the second with a stock token. The pin bump is still to do
  (with J8b).

### `strconv.NumError`'s `Error()` has no spec

- **Missing.** Perennial specifies `strconv.ParseUint`'s errors as fresh `*NumError`s
  (`strconv.numErrorOf`) but not `(*NumError).Error` (`"strconv." + Func + ": parsing " +
  Quote(Num) + ": " + Err.Error()`, through `strconv.Quote`), so a caller that must show the error
  prints (`http.errStrOk`, `zap.Error`'s callers) cannot. Found 2026-10-26 when trying
  `types.IDFromString` (`strconv.ParseUint(s, 16, 64)`): its proof would need a new axiom for
  `NumError.Error` in place of the one it discharges, so it stays an axiom.
- **Workaround here.** None: `types.IDFromString.wp_proof` stays a trust-boundary axiom. Its success
  case is provable over `ParseUint.spec` (a pure lemma that `parseUint (types.idStr x) 16 64 = .ok
  x`, by induction on `types.hexNatF`'s fuel with `parseDigits_append_ok`).
- **Proposed change.** A spec of `(*NumError).Error` (returns some string; or the string, with a
  spec of `Quote`) in Perennial's `Proof/strconv`.

### `errors.Is`/`errors.As` at non-pointer targets and for leaves

- **Missing.** Perennial's `errors.Is.spec` takes a `nil` or pointer target, and its
  `errors.As.spec` allows any result. Four axioms here are specializations it does not cover
  (2026-10-26 survey): `errors.IsDeadlineExceeded` and `errors.IsCtxErr` (the target
  `context.DeadlineExceeded`, an empty struct), `errors.IsStatusErr` (an `EtcdError` value
  target), `errors.AsLeaf` (`As` of an `errors.New` error against a type whose set excludes
  `*errorString` returns `false`).
- **Workaround here.** The four stay trust-boundary axioms (`Proof/errors/`).
- **Proposed change.** `errors.Is.spec` for a comparable non-pointer target (Go's `Is` compares
  with `==` first, which does not panic for a comparable target type), and an `errors.As` spec that
  says `false` for a leaf error not in the target's type set; then the four are proved here.
