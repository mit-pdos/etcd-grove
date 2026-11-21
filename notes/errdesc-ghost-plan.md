# Plan: errors' descriptions, status codes and outgoing metadata as per-run relations (errdesc)

**Status: stages 1, 2a, 2b landed (2026-11-20/21; §6, §8). Originally PLAN, 2026-11-20.** Branch `prove-errdesc/2026-11-20` (worktree `/shared/etcd-grove-wt/prove-errdesc`),
group `errdesc`. Part II of the per-heap redesign (`notes/perheap-scope.md`): Part I (incoming metadata,
`metadata.ctxInMD`) has landed; this plan takes the outline Part II left (revision 2 of the Scope, commit
`3b10ff2b93`: its §1.2-§1.3 inventory, §2.1-§2.2 vocabulary, §3.2-§3.3 old→new tables, and review 2's
decided directions for MAJOR 1 and MAJOR 3) and stages it.

## 0. The problem

`go_etcd_io.etcd.cache.v3.errDesc : GoInterface → GoString`, `EtcdGrove.statusCode : GoInterface → w32` and
`metadata.outgoingOf : GoInterface → GrpcMd` are fixed Lean functions of a Go value; for a pointer error or a
context, the value is a location. The trust-boundary posts of `status.Error`, `status.FromError`,
`metadata.AppendToOutgoingContext`, `withVersion`, the grpc model's contracts and others equate them with data
the caller chooses, for a value the call allocates (or whose method it calls). No implementation can meet such
a post: a fresh allocation may be any location, so two runs of `status.Error(c, "a")` and `status.Error(c, "b")`
from one heap may return the same value, and by adequacy `errDesc` of it would be both (etcd-refimpl
`README.md`, "Findings"; `notes/axiom-review/ctx-descs.md`, "per-execution reading"; the Scope's §0, the rule
(I1)-(I5)). Same for `grpcStatusROP : Loc → w32 → Prop` (code of a status pointer) and `metadata.builtRawMD`
(content of a `rawMD`), the family members of the Scope's §1.3 that sit inside these posts.

## 1. The rule (from the Scope, §0)

- **(I1)** no trusted text has an opaque pure function of a pointer-typed value; a persistent `IProp`
  relation replaces it;
- **(I2)** no entailment concludes a pure fact from such a relation (laws conclude relations, proved);
  no agreement law;
- **(I3)** a pure fact comes only from a triple whose precondition fixes the relation's data before the call;
- **(I4)** the opaque leaves are `IProp`s with no law, given only by posts of uninterpreted calls, and take the
  heap's names (`[hG : HeapGS _ GF]`).

The data a relation carries (a metadata value, a description string) is threaded as a parameter: a spec that
needs to say something about an error's description or a context's metadata takes it as `∀ m`, with the
relation in its precondition, and states the post about `m`.

## 2. Vocabulary

### 2.1 Outgoing metadata (stage 1)

In `Proof/context/LibKeys.lean` / `LibKeysChain.lean`, beside `ctxInMD`:

```lean
/-- (opaque; TRUSTED; no law) grpc's `metadata` made the `rawMD` `v` (`NewOutgoingContext`,
`AppendToOutgoingContext`) whose `FromOutgoingContext` view is `f`, never written after. -/
opaque metadata.builtRawMDRaw [hG : HeapGS HasLC.hasLC GF] (v : GoInterface) (f : GoString → Option (List GoString)) : IProp GF
def metadata.outgoingHeld (v) (md : GrpcMd) : IProp GF :=
  ⌜md = none ∧ v is not a rawMD⌝ ∨ ∃ f, ⌜md = some f⌝ ∗ □ builtRawMDRaw v f
/-- `ctx`'s outgoing metadata is `md` (chain form). SpecPlan's `outMD` (an `Option`: `none` = no metadata). -/
def metadata.outMD (ctx : GoInterfaceOk) (md : GrpcMd) : IProp GF :=
  ∃ v, context.ctxValue ctx mdOutgoingKeyAny (· = v) ∗ outgoingHeld v md
def metadata.outgoingCtxOkC ctx := ∃ md, outMD ctx md                 -- name kept, redefined
def metadata.outgoingCtxOk ctx := ∃ v md, valueAt ctx key (· = v) ∗ outgoingHeld v md   -- WP form, kept name
```

`metadata.builtRawMD` (opaque `Prop`), `metadata.outgoingRes` and `metadata.outgoingOf` are deleted. Laws (all
proved): `outMD_background`/`_todo` (`none`), `_from` (`ctxValueFrom`), `_valueCtx` (another key), `_cancel`,
`_raw` (a context of a type `value()` does not special-case, from the WP form), the WP form from the chain form.

### 2.2 Errors (stage 2)

In `Proof/google_golang_org/grpc/status/` (`ErrDesc.lean`, `StatusRO.lean`), SpecPlan's names:

```lean
/-- (opaque; TRUSTED; no law) `s` is a grpc `*Status` with code `c` and message `m`, never written after
(the producer's guarantee: `grpcStatusRO`'s, `examples/premisefix/grpcstatusro`). -/
opaque status.statusAtRaw [hG] (s : Loc) (c : w32) (m : GoString) : IProp GF
def status.statusAt s c m : IProp GF := ⌜s ≠ null⌝ ∗ □ statusAtRaw s c m        -- replaces grpcStatusRO s c
/-- `e` has grpc's `GRPCStatus() *Status`, which stably returns `s`, a status of code `c`, message `m`. -/
def statusErrIs (e : GoInterfaceOk) (c) (m) : IProp GF
/-- What `status.FromError` sees of `err` (SpecPlan's `errView`): nil (OK, ""), a leaf without
`GRPCStatus` (Unknown, its stable `Error()`), or a status error. -/
def errView (err) (c) (m) : IProp GF
/-- **`err`'s description is `m`**: what `FromError(err).Message()`/`rpctypes.ErrorDesc` return (for an
error without `GRPCStatus`, wrapping or not, its stable `Error()`; with it, its status's message), with the
value pin: of an `rpctypes.EtcdError` value, `m` is its `desc` (I5: a pointer-free value). -/
def descIs (err) (m) : IProp GF
```

`errDesc`, `statusCode`, `grpcStatusROP`, `grpcStatusRO` are deleted. `grpcErrMethodsOk e` gives, for the
`GRPCStatus` method, `∃ s c m, gsReturns e s ∗ statusAt s c m`; for `Is`,
`□ ∀ target m m', descIs (ok e) m -∗ descIs target m' -∗ WP e.Is(target) {b. ⌜b = true → m = m'⌝}`.
Laws (proved): `descIs_nil`, `descIs_etcdError` (replaces the axiom `rpctypes.errDesc_etcdError`, from
`EtcdError.Error`'s proved spec), `descIs_of_errView` (with the pin for non-`EtcdError` types),
`descIs_errorString` (an `*errors.errorString` from its cell), `descIs_ctxErr`, `errorfWrap_descIs`.

## 3. Old → new, per trusted text

### 3.1 Stage 1 (outgoing)

| text | kind | old | new |
|---|---|---|---|
| `metadata.AppendToOutgoingContext.wp_proof` | axiom (names-only) | `⌜outgoingOf c' = mdAdd (outgoingOf ctx) k v⌝` | `∀ md`, pre `outMD ctx md`; post `outMD ci (mdAdd md k v)` |
| `withVersion.wp_proof` | axiom (names-only) | `⌜∃ v, outgoingOf c' = mdSet (outgoingOf ctx) …⌝` | `∀ md`, pre `outMD ctx md`; post `∃ v, outMD ci (mdSet md … [v])` |
| `streamKeyFromCtx.wp_proof` | axiom | `RET streamKeyOf (outgoingOf ctx)` | `∀ md`, pre `outMD ctx md`; `RET streamKeyOf md` |
| `WithRequireLeader.wp_proof` | axiom | `outgoingCtxOkC c` (with `builtRawMD` inside) | the same name, redefined (`∃ md, outMD c md`) |
| `context.WithCancelValCtx.wp_proof` | axiom (P-i) | `⌜outgoingOf ctx' = outgoingOf inctx⌝` | `∀ md`, pre `outMD inctx md`; post `outMD ctx' md` |
| `context.WithTimeoutBackgroundMd.wp_proof` | axiom (P-i) | `⌜outgoingOf ctx' = none⌝` | `outMD ctx' none` |
| `grpcAttemptMd` (in `grpcInvokerOk`, the axiom `ClientConn.Invoke`'s and the model's) | def in trusted contract | over `outgoingOf ctx` | `grpcAttemptMd conn om md` over a metadata value; the invoker's pre takes `outMD ctx om` (`om` the caller's) |
| `newWatcherGRPCStream.spec`, the watch client's invariants (`WsPrm`, `wsRow`, `reqP`, `watcherMu`) | proved | `streamKeyOf (outgoingOf P.ctx)` | the stream's `G.ckey`; a watch's record keeps its caller's metadata (`P.omd`, with `outMD P.ctx P.omd`) |
| `clientAttemptMd`, `attemptPre` (client) | defs | over a context | over its metadata value (`om`) |
| examples `auth`/`authlease` (`akOut`, `reqCtx`, `deliversOutgoing`) | proved specs | `outgoingOf ctx = akOut who` | `outMD ctx (akOut who)` in the pre |

### 3.2 Stage 2 (errors)

| text | kind | old | new |
|---|---|---|---|
| `status.Error.wp_proof` | axiom | `⌜errDesc err = msg⌝` | post `statusErrIs e c msg` (the pin vacuous: a `*status.Error`) |
| `status.FromError.wp_proof` | axiom | `Code()` = `statusCode err`, `Message()` = `errDesc err`, `ok = false → errDesc err = m` | `∀ err c m`, pre `statusErrOk err ∗ errView err c m`; `Code()` returns `c`, `Message()` `m` |
| `status.Code.wp_proof` | axiom | post `True` | unchanged text; `statusErrOk` changes meaning |
| `status.Status.Code.wp_proof` | axiom | pre `grpcStatusRO s c` | pre `statusAt s c m` |
| `errors.IsStatusErr.wp_proof` | axiom (P-i) | `b = true → errDesc err = errDesc target ∧ T3` | `∀ m m'`, pre `descIs err m ∗ descIs target m'`; `b = true → (err = target ∨ m = m') ∧ T3` (B1: Go's `==` shortcut reads no description) |
| `fmt.ErrorfWrap` (proved) | theorem | `Unwrap → pre <+: errDesc err` | conjunct deleted; `errorfWrap_descIs` (proved law) |
| `rpctypes.errDesc_etcdError` | axiom | pure | deleted; `descIs_etcdError` (proved) |
| `v3rpc.toGRPCErrorMap_init` / `grpcErrMapOk` | axiom | pure `errDesc` facts of pointer keys and values | an `IProp`: each key and value with its `descIs`, the same pure facts about those descriptions |
| `grpc.model.respond.wp_proof` | axiom (model) | `⌜err ≠ nil ∧ errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)` | `∀ m`, pre `descIs err m ∗ (⌜err ≠ nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m)` |
| handler outcome in `grpcMethodOkMd`, `grpcHandlerOk*`, `srvInterceptorOk`, `grpcDecOk`, `grpcInvokerOk` | defs in trusted contracts | `errDesc err ∈/∉ handlerDescs` | `∃ m, descIs err m ∗ …` in posts; the invoker's error a fresh `*status.Error` or `io.EOF` (review 2's MAJOR 1, direction (a)) |
| `waitRetryBackoff.wp_proof` | axiom | `errDesc err ∉ handlerDescs` | `∃ m, descIs err m ∗ ⌜m ∉ handlerDescs⌝` |
| `rpctypesInit` (package facts, proved by the translated initializer) | def | `errDesc e = lit` | `descIs (ok e) lit` (the `ErrGRPC*`: from `status.Error`'s post); the `EtcdError`s keep their pure `x.desc` |
| `noRefusal`, `notReadDesc`, `ctxErrDescs`, `grpcErrOut`, `rangeErrDesc`, `rangeKeysErr`, `ifcErrOut`, `rangeErrOut`, `readErrIs`/`listErrF` (k8s) | defs | pure over `errDesc err` | `∃ m, descIs err m ∗ P m` (posts) / `∀ m` parameters (pres) |
| `rpctypes.Error`/`ErrorDesc`, `ContextError`, `isSafeRetry*`, `shouldRefreshToken`, `isHaltErr`, `leasingKV.acquire`, k8s `listReadError` (proved) | specs | over `errDesc`/`statusCode` | `∀ m` (or `c m`) in the pre, the post about them (the Scope's §3.3 restated chains) |

## 4. Stages (each landed green)

1. **Outgoing metadata** (`outgoingOf`, `builtRawMD` gone). ~40 files: `LibKeys`, `LibKeysChain`, grpc
   `metadata` specs, `InvGrpc` (`grpcAttemptMd`, `grpcInvokerOk`), client `withVersion`, `streamKeyFromCtx`,
   `WithRequireLeader`, `InvKVConn`, `InvClientAuth`, the watch client (`InvWatch`, `watcher__Watch`,
   `newWatcherGRPCStream`, `newWatchClient`, `WatchRun`, `WatchRecon`, `WatchCheck`, `RequestProgress`),
   `context` `WithCancelValCtx`/`WithTimeoutBackgroundMd`, `TimeoutCtx`, examples `auth`/`authlease`.
   Axioms: statements of 6 change, none added. Estimate 2-3 days.
2. **Errors** (`errDesc`, `statusCode`, `grpcStatusRO(P)` gone; `errDesc_etcdError` becomes a theorem: -1
   axiom). ~60 files. One flow (server producers → handler outcome → grpc model → invoker → client consumers)
   whose only cut is the grpc model (it relays a description string), so possibly two landings:
   2a the vocabulary, `status`/`errors`/`rpctypes`/`fmt`, the server side and the model's server half;
   2b the invoker and the client (`InvKVConn`, `KVService`, `ContextError`, retry, k8s, leasing).
   Estimate 5-8 days.

Each stage: `etc/tcb-report.py --check` (axiom count must not increase; names unchanged but
`errDesc_etcdError` out in stage 2), collections, `etc/gen-interface.py` for the packages with an API list,
`notes/decisions.md` (supersedes "`errDesc` in a module of its own" and D29's "function of the error"),
`notes/axiom-review/ctx-descs.md` (the per-execution reading retired), the ledger (convergence with
SpecPlan's `outMD`/`errView`/`statusAt`: the `Option` metadata and `descIs`, already recorded 2026-11-18).

## 5. Risks

- **Agreement-dependent proofs.** Without agreement two relations on one value give unrelated data. Every proof
  must carry the one datum the producer fixed (the caller's metadata into a watch's record, the handler's
  description into the grpc model, `rpctypes.Error`'s `m` to `shouldRefreshToken`'s comparison). Where Go
  compares by identity, the value pin (an `EtcdError` value) or the target's own `descIs` gives the
  description (the Scope's §3.3).
- **Closed statements.** No top-level statement names `errDesc`/`outgoingOf` (checked: the `Results` files
  only rebuild); the examples' auth specs take `outMD` in place of a pure equation (they are proved, not
  trusted).
- **Concurrent landings** touch `InvGrpc.lean`, `cache/v3/Base.lean`, `rpctypes`: merge `lean` often.

## 6. Stage 1 as landed (2026-11-20)

- `metadata.builtRawMDRaw v f` (opaque `IProp`, `{hlc}`-generic, `LibKeys.lean`), `metadata.outgoingHeld v md`,
  `metadata.outMD ctx md` (chain form, `LibKeysChain.lean`); `outgoingCtxOkC ctx := ∃ md, outMD ctx md`,
  `outgoingCtxOk` (WP form) `∃ v md, valueAt … ∗ outgoingHeld v md`. Laws: `outMD_background`/`_todo`/`_from`/
  `_valueCtx`/`_ownKey`/`_raw`/`_bgFrom`/`_todoFrom`, `outgoingCtxOkC_of_outMD`, `outgoingCtxOk_of_outMD`,
  `watchCtx_outMD`, `txnObjAt_outMD`.
- The metadata travels as a parameter `om : GrpcMd`, always bound right after its context (`ctx om cd`), with
  `metadata.outMD ctx om` just before `ctxOk ctx cd` in the precondition. Contracts indexed by a context
  became indexed by `om` (`attemptPre conn om`, `clientAttemptMd conn om md`, `clientOpAuOn s E ρ conn om`,
  `clientGrant`, `clientHistAu`, `txnUpdAtOn`, `doRunGen`, `watchCheckOk`). A caller indifferent to the
  metadata takes one from `ctxOk` (`ctxOk_outgoingC`) or `watchCtx` (`watchCtx_outMD`).
- The examples' `hout : outgoingOf ctx = akOut who` became `metadata.outMD ci (akOut who)` in the laws'
  preconditions (auth) or a metadata-typed index with `ctx = akOut who` (authlease); `reqCtx_out` is gone
  (`reqCtx`'s post gives `outMD ci (akOut who)` up to unfolding `akOut`).
- Not done: `WithCancelValCtx` and `WithTimeoutBackgroundMd` stay axioms (restated); both are provable from
  Perennial's `WithCancel`/`WithTimeout` models plus the chain laws (the Scope's m6/Q6), a follow-up that
  removes two axioms.

## 7. Stage 2, the concrete design (for the implementer)

The same discipline as stage 1: the description travels as a parameter `m : GoString` next to its error,
with a relation in the precondition; posts of producers give `∃ m, descIs err m ∗ P m`.

1. **Vocabulary** (`Proof/google_golang_org/grpc/status/StatusRO.lean`, `ErrDesc.lean`):
   `opaque status.statusAtRaw (s : Loc) (c : w32) (m : GoString) : IProp GF` ({hlc}-generic, no law);
   `statusAt s c m := ⌜s ≠ null⌝ ∗ □ statusAtRaw s c m` (replaces `grpcStatusRO s c`);
   `statusErrIs e c m := ⌜GRPCStatus ∈ e.ty⌝ ∗ ∃ s, (□ GRPCStatus() returns s) ∗ statusAt s c m`;
   `errView err c m ok` (SpecPlan's: nil/OK/""/true, a leaf without `GRPCStatus` with `errorMsgIs e m`,
   `Unknown`, false, or `statusErrIs e c m`, true); `descIs err m` (nil and `""`; no `GRPCStatus` and
   `errorMsgIs e m`; or `∃ c, statusErrIs e c m`; with the `EtcdError` pin
   `∀ y, err = mkOk EtcdError.ty #y → m = y.desc`).
2. **`statusErrOk`** (`cache/v3/Base.lean`): its `∃ m, errorMsgIs e m` gains the pin
   (`∃ m, errorMsgIs e m ∗ ⌜pin e m⌝`), and `grpcErrMethodsOk`'s `GRPCStatus` clause gives
   `∃ s c m, (□ returns s) ∗ statusAt s c m`; `Is` gives
   `□ ∀ target m m', descIs (ok e) m -∗ descIs target m' -∗ WP e.Is(target) {b. ⌜b → m = m'⌝}`.
   Laws: `statusErrOk_errView : statusErrOk err ⊢ ∃ c m ok, errView err c m ok`,
   `statusErrOk_descIs : statusErrOk err ⊢ ∃ m, descIs err m` (what a caller indifferent to the
   description uses), `descIs_of_errView` (with the pin from `statusErrOk`), `descIs_etcdError`
   (proved from `EtcdError.Error`'s spec; replaces the axiom `rpctypes.errDesc_etcdError`).
3. **Axioms restated** (no new one): `status.Error` (post `statusErrIs e c msg`, the type and pointer facts
   kept), `status.FromError` (`∀ err c m ok`, pre `statusErrOk err ∗ errView err c m ok`; `Code()` returns `c`,
   `Message()` `m`), `status.Status.Code` (pre `statusAt s c m`), `errors.IsStatusErr` (`∀ m m'`, pre
   `descIs err m ∗ descIs target m'`; `b → (err = target ∨ m = m') ∧ T3`), `grpc.model.respond`
   (`∀ m`, pre `descIs err m ∗ (⌜err ≠ nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m)`), `waitRetryBackoff`
   (`∃ m, descIs err m ∗ ⌜m ∉ handlerDescs⌝`), `v3rpc.toGRPCErrorMap_init` (`grpcErrMapOk` an `IProp`: every
   key and value with a `descIs` meeting today's pure facts).
4. **The handler outcome** becomes a definition `handlerErrOut Ψe err := ∃ m, descIs err m ∗
   (⌜err ≠ nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m)` replacing the literal text in `grpcMethodOkMd`,
   `grpcHandlerOk*`, the handler specs and `UnaryHandlerLemmas` (one `sed`), with laws `handlerErrOut_nil`
   and `handlerErrOut_all` (from `□ ∀ d, Ψe d` and `statusErrOk_descIs`/`srvErrOk`). `grpcDecOk` and
   `srvInterceptorOk` (`errDesc err ∉ handlerDescs`) become `∃ m, descIs err m ∗ ⌜m ∉ handlerDescs⌝`
   (`notHandlerErr err`), with a law from `ctxErrIs`. The invoker's error outcome (`grpcInvokerOk`) gives
   `handlerErrOut Ψe err` and `noRefusal` restated `err = nil ∨ ∃ m, descIs err m ∗ ⌜m ∉ refusalDescs⌝`.
5. **Client chains** (the Scope's §3.3): `rpctypes.Error`/`ErrorDesc` pre `descIs err m`, post `descIs err' m`;
   `shouldRefreshToken`/`isSafeRetry*` pre `descIs err m`, post `b → m ∈ refusalDescs` (the identity branch
   closed by the pin: the targets are `EtcdError` values, and `ErrGRPCNotSupportedForLearner`'s own
   `descIs` from `rpctypesInit`); `ifcErrOut` over `m`; k8s `listReadError`/`readErrIs` and
   `KVService.rangeErrOut` carry `∃ m, descIs err m ∗ …`.
6. **Server chains**: `rangeErrDesc`, `grpcErrOut`, `notReadDesc`, `ctxErrDescs`, `mvcc.rangeKeysErr`
   (`errorfWrap_descIs` replaces `ErrorfWrap`'s conditional `pre <+: errDesc` conjunct, which goes).
7. **Order**: 1-2 (vocabulary; everything rebuilds), 3 (axioms), 4 (handler outcome, mostly textual), then the
   chains 5-6 file by file from the build's errors, as stage 1 went. Estimate 4-6 days.

## 8. Stage 2b as implemented (2026-11-21, branch `prove-errdesc2b/2026-11-21`)

`go_etcd_io.etcd.cache.v3.errDesc` and its two modules (`Proof/google_golang_org/grpc/status/ErrDesc.lean`,
`Proof/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/ErrDesc.lean`) are gone; the axioms `rpctypes.errDesc_etcdError` and
`rpctypes.errDesc_wrapError` (fmtmodel's, 2026-11-20, `ErrDescWrap.lean`) with them, and
`context.WithTimeoutBackgroundMd` is proved (from Perennial's `wp_WithTimeout_Background` and stage 1's
`outMD_bgFrom`): −3 axioms, none or `sorry` added. Departures from §7, each simpler or forced:

- **`descIs err m`** (`cache/v3/Base.lean`, next to `errorMsgIs`): nil and `""`; an `EtcdError` value
  `mkOk EtcdError.ty #x` and `m = x.desc'` (the value pin is a disjunct, not a side condition: the producer
  law `descIs_etcdError` is definitional, the pin `descIs_etcdError_eq` needs only that the value determines
  its `desc`, from `EtcdError.TypeAssumptions.get_desc`'s determinism); otherwise (not an `EtcdError` value)
  no grpc `GRPCStatus` and `errorMsgIs e m`, or `GRPCStatus` stably returning `s` with `statusAt s c m`.
  No `errView` and no `statusErrIs`: `status.FromError` takes `descIs err m` and stage 2a's
  `statusCodeIs err c` side by side; `status.Error`'s post gives `descIs err msg`. `statusErrOk` is unchanged
  but for its `Is` clause (below); `statusErrOk_descIs`, `srvErrOk_descIs` (through `ctxWrapErr_descIs`) give
  some description to a caller indifferent to it.
- **`errors.IsStatusErr`**: `∀ err target (dm : Option (GoString × GoString))`, pre `isDescs err target dm`
  (`none`: nothing, for the ten callers indifferent to descriptions; `some (m, m')`: `descIs err m ∗
  descIs target m'`), post `b → (∀ m m', dm = some (m, m') → err = target ∨ m = m') ∧ T3`. The identity
  disjunct is B1 (Go's `==` reads no description). `grpcErrMethodsOk`'s `Is` clause: `□ ∀ target m m',
  descIs (ok e) m -∗ descIs target m' -∗ WP e.Is(target) {b. b → m = m'}`.
- **The learner's identity branch** (not in §7, which assumed it closed by the initializer's `descIs`): with
  no agreement law, `err = ErrGRPCNotSupportedForLearner`'s value and `descIs err d` (the invoker's, `d` no
  refusal) say nothing of each other, so `isSafeRetry`'s `b → d ∈ refusalDescs ∨ p = 0` failed in the branch
  where `errors.Is` answers `true` by `==`. `grpcInvokerOk`'s error post gains `notLearnerErr err` (the
  invoker's error is never that package variable's value: grpc builds its status errors from the wire,
  `status.FromProto(...).Err()`, a fresh `*status.Error`, or returns `io.EOF`/the context's error; it imports no
  etcd package), `isSafeRetry`'s pre takes it, and the branch is absurd. A strengthening of the
  `ClientConn.Invoke` axiom's post (through `grpcInvokerOk`), true of grpc-go; recorded in `notes/decisions.md`.
- **The handler outcome** `handlerErrOut Ψe err := ∃ m, descIs err m ∗ (⌜err ≠ nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m)`
  and `notHandlerErr err := notDescIn handlerDescs err` (`InvGrpc.lean`); laws `handlerErrOut_nil`, `_not`, `_all`,
  `_allS` (from `statusErrOk`), `_allSrv` (from `srvErrOk`; takes `ErrorStringLeaf`), `_mono`. `grpcDecOk`,
  `srvInterceptorOk`, `waitRetryBackoff` (`⌜err = nil⌝ ∨ notHandlerErr err`) use `notHandlerErr`.
- **The invoker's error** (`grpcInvokerOk`): `notLearnerErr err ∗ ∃ d, descIs err d ∗ ⌜kvMethod ∧ noRefusalAt →
  d ∉ refusalDescs⌝ ∗ (⌜d ∈ handlerDescs⌝ -∗ Ψe d)` (`noRefusal`, a pure fact of `errDesc`, is gone).
- **Server chains**: `grpcErrMapOk M kf kc` is an `IProp` (`⌜grpcErrMapKeys M kf kc⌝`: non-nil values, `kf`,
  `kc` keys; and `□` per entry: the value's description `mv` with `mv = F → k = kf`, `mv = C → k = kc`, the
  key's `mk ∉ {F, C}`); laws `grpcErrMapOk_ne`, `_key`, `_val`. The keys' own `mvcc: …` descriptions are no
  longer needed: `kf ≠ kc` from their message cells, a `rangeKeys` `*fmt.wrapError` apart from mvcc's
  `*errorString`s by its `Unwrap` method. `grpcErrOut`'s fallback, `ctxErrDescs`, `notReadDesc` (now
  `notDescIn [F, C]`), `rangeErrDesc`, `mvcc.rangeKeysErr` (its description conjunct dropped: the prefix comes
  from `errorfWrap_descIs`, proved in `Base.lean`) carry `descIs`. `fmt.ErrorfWrap`'s post lost its conditional
  `errDesc` conjunct.
- **Client chains**: `rpctypes.ErrorDesc` (pre `descIs err m`, `RET #m`), `rpctypes.Error` (pre `descIs err m`;
  post `descIs err' m` and `err' = err ∨ an EtcdError of desc m`, for every error), `ContextError` (pre
  `descIs err m`, post with `descIs err' m`), `shouldRefreshToken`/`isSafeRetry`/`isSafeRetryMutableRPC`
  (`descIs err m` in, `b → m ∈ refusalDescs` out), `ifcErrOut` (`∃ d, descIs err d ∗ …`; laws `_intro`,
  `_notin`, `_of_attempt`, `_absurd`), `KVService.rangeErrOut`, `kubernetes.rangeErrSound`, k8s `readErrIs`
  (`∃ d, descIs err d ∗ □ (⌜d = futureRevDesc⌝ -∗ …)`), `store.listReadError` (the identity branch through the
  pin). `kv.Get` fixes the description `ContextError` keeps before its call by a case on `sortValid`.
- **rpctypes' initializer** (`etc/gen-init.py`): the `ErrGRPC*` descriptions from `status.Error`'s post (`DR<x>`,
  restated for the named `futureRevDesc`/`compactedDesc`), the map literal built under
  `□ ∀ k v, M !! k = some v → descIs v k` (`ErrorDesc(e)` returns the literal), `Err* = Error(ErrGRPC*)` an
  `EtcdError` of the literal `desc`.

Not done: `context.WithCancelValCtx` remains an axiom: its parent is a `*valCtx` outside Perennial's
context model, whose `WithCancel` takes an `isContext` parent (the `Value` contract of
`notes/perennial-changes.md`).
