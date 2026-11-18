# Scope: the per-heap redesign — pointer-keyed pure functions become per-run Iris relations

**Status: SCOPE, for independent review (hard stop). No Lean changed in the tree.** Approved to be written
by the user 2026-11-18 via etcd-grove-03. Branch `perheap-scope` off `lean` `49bd7924e6` (worktree
`/shared/etcd-grove-incomingof`), the perheap agent of etcd-grove-03. Background: `notes/axiom-review/
ctx-descs.md`, `notes/axiom-review/incomingof.md` (Part A refuted), `notes/axiom-review/incomingof-b.md`
(Part B, T1–T8'), `notes/incomingof-crossworld.md`, `notes/fromerror-wand.md`, `notes/incomingof-scope.md`
(§0, A-D, Q1). Lean probe (throwaway, not in the tree): `/shared/tmp/perheap/Probe.lean`, checked with
`lake env lean` at this head, no errors (§2.4).

**The goal (the user's):** no trusted text concludes a pure fact about a pointer-typed value. Replace the
opaque Lean functions of a heap-dependent value (`metadata.incomingOf`, `metadata.outgoingOf`,
`errDesc`, `statusCode`, and the rest of the family, §1.3) by per-run Iris relations, so that every pure
fact a trusted text gives is about a value fixed in a precondition or returned by the call (a string, a
metadata map value, a code), never an equation about an opaque function of a pointer.

---

## 0. The rule, restated for the redesign

A trusted fact about the Go meaning of a pointer-typed value `x` (a context, an error, a `*Status`, an
`MD` map) is true only of the heap of one execution. Three ways turn such a fact into a Lean fact about
every heap (all three are now on record):

- **(a) crossWorld** (`ctx-descs.md`): an entailment whose left side is bare persistent points-tos holds
  in a fresh heap with any content.
- **(b) the persistent-authoritative fresh world** (`incomingof.md`, "The refutation"): a fresh world
  owning `Auth DFrac.discard σ` decides every points-to by `σ` and satisfies every WP of a non-value, so
  any wand from cells (or WP forms) to a pure fact holds there by the choice of `σ`.
- **(c) adequacy with allocation** (`incomingof-scope.md` §0.2): a pure fact in the post of code with
  Lean semantics, about an address the code allocated, becomes a Lean fact for every address the
  allocator may return; two closed runs then join.

The redesign's invariant, which every new text below is checked against:

> **(I1)** No trusted text has an opaque *pure* function of a pointer-typed value. Opaque functions of
> that kind are deleted; what replaces them is an `IProp` relation `R x a` (persistent).
> **(I2)** No entailment (axiom, premise-class field, law) concludes a pure fact from such a relation:
> its conclusions are relations again (transfer laws), and the transfer laws are *proved*, not assumed,
> wherever the relation is defined.
> **(I3)** A pure fact about `a` comes only from a triple whose precondition holds `R x a` with `a` fixed
> before the call (the fromerror-wand lesson), and is about `a` and the call's results; never a wand in a
> post that takes `R x a'` later.
> **(I4)** The only opaque leaves are `IProp`s made by trusted producers (posts of uninterpreted calls),
> with **no law** (no agreement, no transfer), so no proof and no fresh world can build or combine them.

(I2)+(I4) defeat (a) and (b): a fresh world may build relations (it satisfies WP forms and, with a
discarded authority, points-tos), but no law lets it extract a pure fact; the pure facts sit in triple
posts, which are vacuous in such a world and are never Lean facts. (I3) defeats (c): a post of interpreted
code states a pure fact about `a`, a precondition parameter tied to that run's resources, not about the
pointer; two runs with the same address give facts about their own `a`s, which no Lean statement joins.

---

## 1. Inventory (at `lean` `49bd7924e6`)

### 1.1 The four primary opaque functions

| opaque | declared | files (Spec / Proof) | occurrences |
|---|---|---|---|
| `metadata.incomingOf : GoInterface → GrpcMd` | `Proof/google_golang_org/grpc/metadata/Incoming.lean:27` | 41 (21 / 20) | 81 |
| `metadata.outgoingOf : GoInterface → GrpcMd` | `Proof/google_golang_org/grpc/metadata/Outgoing.lean:31` | 31 (7 / 24) | 88 |
| `errDesc : GoInterface → GoString` | `Proof/google_golang_org/grpc/status/ErrDesc.lean:25` | 48 (28 / 20) | 176 |
| `statusCode : GoInterface → w32` | `Proof/google_golang_org/grpc/status/StatusRO.lean:24` | 6 (2 / 4) | 13 |

Union: **100 files** mention one of the four (94 with a declaration that does, by the declaration scan
`/shared/tmp/perheap/decls.py`). Derived pure vocabulary built on them (each must move too):
`auth.ctxTokenOf` (`server/v3/auth/InvAuth.lean:748`, `match incomingOf ctx`; 28 files, 119 occ),
`deliversOutgoing` (examples auth `ClientAuth.lean:98`), `grpcAttemptMd` (`grpc/InvGrpc.lean:1595`),
`clientAttemptMdOf` (`client/v3/InvKVConn.lean:1317`), `grpcErrMapOk` (`v3rpc/Base.lean:130`),
`notReadDesc` (`v3rpc/Base.lean:300`), `ctxErrDescs` (`v3rpc/Base.lean:232`), `grpcErrOut`
(`v3rpc/InvKV.lean:340`), `rangeErrDesc` (`etcdserver/ReadOn.lean:294`), `rangeKeysErr`
(`mvcc/InvStore.lean:5632`), `noRefusal` (`cache/v3/Base.lean:78`), `ifcErrOut`
(`client/v3/InvKVConn.lean:1371`), `rangeErrOut` (`client/v3/KVService.lean:1023`), `rangeErrSound`, `limN`
(`client/v3/kubernetes/Defs.lean:314, 296`), `readErrIs` (`k8s etcd3/ListDefs.lean:368`), the handler
outcome clause `⌜err ≠ nil ∧ errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)` (in every handler contract).
Pure functions of a *metadata value* (`mdTokenOf`, `mdVals`, `mdAdd`, `mdSet`, `streamKeyOf`) are not of
the family: their argument is a Lean value, not a pointer; they stay.

### 1.2 Trusted texts that state pure facts about them

Kind: **E** entailment (axiom/law/premise field); **P-u** post of a triple over uninterpreted code
(names-only or model-only); **P-i** post of a triple over code with Lean semantics (translated, or a
Perennial trusted model with an `impl`); **D** a definition inside a trusted statement (the grpc model's
contracts). Exposure: which of (a)/(b)/(c) of §0 reaches it.

| trusted text | file:line | kind | fact | exposure |
|---|---|---|---|---|
| `incomingOf_cancelCtx` | `grpc/metadata/Incoming.lean:61` | E | `ctxField c ↦□ p ⊢ ⌜incomingOf (*cancelCtx c) = incomingOf p⌝` | (a) **refuted** (`incomingOf_const`) |
| `v3rpc.incomingOf_cancellableContext` | `v3rpc/WrapperMd.lean:76` | E | same for etcd's wrapper | (a) **refuted** in meaning |
| `metadata.FromIncomingContext.wp_proof` | `Proof/google_golang_org/grpc/metadata/FromIncomingContext.lean:23` (spec `Spec/…:37`) | P-u | `ok ↔ incomingOf ctx ≠ none`, result = `incomingOf ctx` | per run only |
| `context.WithValue.wp_proof` | `Proof/context/WithValue.lean:24` (spec `Spec/context/WithValue.lean:51`) | P-u (WithValue has no body in Perennial) | `incomingOf c' = incomingOf parent` | per run only |
| `traceutil.Tracer.Start.wp_proof` | `Proof/go_etcd_io/etcd/pkg/v3/traceutil/Tracer__Start.lean:26` | P-u | `incomingOf ctx' = incomingOf ctx` | per run only |
| `metadata.AppendToOutgoingContext.wp_proof` | `Proof/google_golang_org/grpc/metadata/AppendToOutgoingContext.lean:25` | P-u | `outgoingOf c' = mdAdd (outgoingOf ctx) k v` | per run only |
| `withVersion.wp_proof` | `Proof/go_etcd_io/etcd/client/v3/withVersion.lean:27` | P-u (names-only) | `outgoingOf c' = mdSet (outgoingOf ctx) …` | per run only |
| `streamKeyFromCtx.wp_proof` | `Proof/go_etcd_io/etcd/client/v3/streamKeyFromCtx.lean:37` | P-u | `RET streamKeyOf (outgoingOf ctx)` | per run only |
| `context.WithCancelValCtx.wp_proof` | `Proof/context/WithCancelValCtx.lean:38` | **P-i** (`WithCancel.impl`) | `outgoingOf ctx' = outgoingOf inctx`, `ctx'` allocated | **(c)** in form (no conflicting fact found: only `none`/equalities reach interpreted posts) |
| `context.WithTimeoutBackgroundMd.wp_proof` | `Proof/context/WithTimeoutBackgroundMd.lean:27` | **P-i** (`WithTimeout.impl`) | `outgoingOf ctx' = none`, `ctx'` allocated | **(c)** in form (as above) |
| `status.FromError.wp_proof` | `Proof/google_golang_org/grpc/status/FromError.lean:29` | P-u | `Code()` returns `statusCode err`, `Message()` `errDesc err`, `ok = false → errDesc err = m` | per run only |
| `status.Error.wp_proof` | `Proof/google_golang_org/grpc/status/Error.lean:26` | P-u | `errDesc err = msg` (allocated `*status.Error`) | per run only |
| `errors.IsStatusErr.wp_proof` | `Proof/errors/IsStatusErr.lean:25` | **P-i** (`errors.Is` translated) | `b = true → errDesc err = errDesc target` | **(c)** |
| `fmt.ErrorfWrap.wp_proof` | `Proof/fmt/ErrorfWrap.lean:32` | **P-i** (Perennial's trusted `fmt.Errorf` model) | `pre <+: errDesc err`, `err` allocated by the call | **(c), with a conflict: finding F1 below** |
| `grpc.model.respond.wp_proof` | `Proof/google_golang_org/grpc/model/respond.lean:25` | P-u (model-only) | pre: `errDesc err ∈ handlerDescs -∗ Ψe (errDesc err)` | per run only |
| `waitRetryBackoff.wp_proof` | `Proof/go_etcd_io/etcd/client/v3/waitRetryBackoff.lean:26` | P-u | `errDesc err ∉ handlerDescs` | per run only |
| `rpctypes.errDesc_etcdError` | `Proof/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/ErrDesc.lean:26` | E (pure, no antecedent) | `errDesc (EtcdError x) = x.desc` | location-free (sound) |
| 16 `rpctypes` initializer axioms (`ErrFutureRev_init` … `ErrGRPCNoLeader_init`) | `rpctypes/Init.lean:150-265` | P-u (uninterpreted `.init`) | `errDesc e = <literal>` of the variable's value (`*status.Error`s are pointers) | per run only |
| `errStringToError_init` | `rpctypes/Init.lean:170` | P-u | `∀ k v, m !! k = some v → errDesc v = k` | per run only |
| `v3rpc.toGRPCErrorMap_init` | `v3rpc/Init.lean:112` | P-u | `grpcErrMapOk M kf kc` (pure `errDesc` facts of the map's pointer keys and values) and the wand `globalAddr g ↦□ k -∗ ⌜(M !! k).isSome⌝` | per run only; the wand is (b)-shaped but sits in a post (Part B T6, M4) |
| `rpctypesInit` (package fact, made by the initializer from the axioms above) | `cache/v3/Base.lean:444` | D | `errDesc (ErrFutureRev) = …`, `errDesc (ErrGRPCNotSupportedForLearner) = …` | inherits |
| `grpcErrMethodsOk` / `statusErrOk` / `srvErrOk` | `cache/v3/Base.lean:374, 405` | D | `grpcStatusRO s (statusCode e)`; `Is` → `errDesc e = errDesc target` | inherits |
| grpc model contracts: `grpcAccepted` | `grpc/InvGrpcRun.lean:134` | D (post of `acceptRun`/`acceptRunConns`) | `▷ Spec (incomingOf ci) …`, `□ Spec (incomingOf ci) γs Dn` | per run only |
| `grpcHandlerOkMd`, `grpcHandlerOwnOkMd`, `grpcMethodOkMd`, `grpcRunOkMd`, `srvInterceptorOk`, `grpcDecOk` | `grpc/InvGrpc.lean:296, 364, 595, 980, 657, 546` | D | `Spec (incomingOf ci)`; handler outcome at `errDesc err` | per run only |
| `grpcStreamHandlerOk`, `grpcStreamMethodOk`, `grpcStreamRunOk`, `srvStreamInterceptorWOk` | `grpc/InvGrpcStream.lean:869, 1235, 1284, 1073` | D | `Spec (incomingOf ci)`; `⌜incomingOf ci' = incomingOf ci⌝` | per run only |
| `grpcInvokerOk`, `grpcAttemptMd` | `grpc/InvGrpc.lean:1678, 1595` | D | attempt metadata from `outgoingOf ctx`; outcome at `errDesc err` | per run only |
| `metadata.transportMD`, `builtRawMD` (opaque `Prop`s of an `MD`/`rawMD` value, a map pointer) | `Proof/context/LibKeys.lean:57, 65` | opaque, in `libCtxOk(C)`, `srvRawStreamIs`, `AppendToOutgoingContext` | "grpc made it" | family (§1.3) |
| `grpcStatusROP` (opaque `Prop` of a `*Status`) | `grpc/status/StatusRO.lean:27` | opaque, in `grpcErrMethodsOk` | read-only with code `c` | family (§1.3) |

**Finding F1 (soundness, in meaning; same class as Scope §0.2, not formalized).** `fmt.ErrorfWrap.wp_proof`
states `pre <+: errDesc (GoInterface.ok err)` of the error `fmt.Errorf` *allocates*, and `fmt.Errorf` has
Lean semantics (Perennial's trusted model with an `impl`). Two closed programs, `Errorf("A%w", e)` and
`Errorf("B%w", e)` (`e = errors.New("x")`, interpreted), may allocate the result at the same address;
adequacy then gives `"A" <+: errDesc v` and `"B" <+: errDesc v` for the same interface value `v`, i.e.
`False`, as a Lean fact. Formalizing it needs a Lean proof that such an execution exists (as for §0.2).
`errors.IsStatusErr.wp_proof` (`errors.Is` translated) is (c)-exposed the same way when combined with such
a fact. The redesign fixes both (§3.3); no separate repair is proposed (Q8). Not yet in `notes/audit.md`.

**Closed and exported statements.** No closed (Adequacy/MainLinked) statement mentions any of these or the
derived vocabulary (scan of every `Results.lean`/`Adequacy*.lean`/`MainLinked.lean`/`Robust*.lean`).
Exported statements that do (text changes, §4): `client_range_any` (`client/v3/Results.lean:2865`, through
`rangeErrOut`), `put_end_to_endM`, `deleteRange_end_to_endM`, `range_end_to_endM`, `txn_end_to_endM`,
`authWrapOut_userAdd` (`v3rpc/Results.lean:392-862`, through `auth.ctxTokenOf`), `authkv_bad_unbound`
(examples auth `Results.lean:123`, `deliversOutgoing`, `outgoingOf`). (`v3rpc`'s watch results mention
`mdTokenOf`, a function of a metadata value: unchanged.)

**Collections reached** (`etc/tcb-collections/*.txt`, 68 in all): the two `incomingOf` axioms, 22
(auth3, authN, authkv, cachekv, compactkv, k8scompactor, k8setcd3, leaseN, leasecatchup, leaseexpiry,
leaseexpiryN, leasekv, linkv3p, linkvtxn, m2, putget, putget3, putgetN, txnlinfaultsN, v3rpc, watch,
watchkv); `FromIncomingContext` 23; `WithValue` 35; `Tracer.Start` 31; `status.FromError` 32 (adds
concurrency, lease, cache, slice, client, cache-client, k8s, k8s-compactor, leasing, lease-served,
recipes); `status.Error` 32; `IsStatusErr` 29; `ErrorfWrap` 36; `respond` 20; `errDesc_etcdError` 31;
the `rpctypes`/`toGRPCErrorMap` initializers 23–24; `withVersion` 22; `waitRetryBackoff` 22;
`streamKeyFromCtx` 14; `WithCancelValCtx` 14; `AppendToOutgoingContext` 3; `WithTimeoutBackgroundMd` 3.
In short: every closed etcd and k8s theorem that serves a request.

### 1.3 The rest of the family

Every other `opaque` to a pure type whose argument holds a `Loc`, a `GoInterface` or a pointer-carrying
value was classified (read-only sweep by a subagent, 2026-11-18; spot-checked). Verdicts: **(i)** same
flaw (a trusted entailment, or a post of interpreted code, concludes the pure fact); **(ii)** per-run only
(heap-dependent, given only by posts of uninterpreted calls: sound per execution, not in Iris's model);
**(iii)** not of the family (identity- or type-keyed, or a function of pure data).

| opaque | declared | trusted sources of its pure fact | verdict | in the redesign |
|---|---|---|---|---|
| `grpcStatusROP` (`*Status` read-only with code `c`) | `grpc/status/StatusRO.lean:27` | `status.Error`, `ErrGRPC*_init`, `toGRPCErrorMap_init`, grpc model posts, inside `grpcErrMethodsOk` | ii | **replaced** (`grpcStatusRaw`, step 2) |
| `metadata.transportMD`, `metadata.builtRawMD` | `Proof/context/LibKeys.lean:57, 65` | `grpcRunCtx`/`grpcAccepted` (model), `AppendToOutgoingContext` | ii | **replaced** (`transportMDRaw`, `builtRawMDRaw`, steps 1, 3) |
| `peer.transportPeer` | `LibKeys.lean:73` | `grpcRunCtx` (model) | ii | step 4 (Q7) |
| `trace.otelSpan` | `LibKeys.lean:103` | `grpcRunCtx`, `Tracer.Start`, k8s `tracing.Start`, `otelgrpc.NewServerHandler` (all names-only) | ii | step 4 (Q7) |
| `utiltrace.builtTrace` | `k8s apiserver audit/CtxKeys.lean:60` | k8s `tracing.Start` (names-only) | ii | step 4 (Q7) |
| `vecLabels` (prometheus, k8s metrics) | `prometheus/Labels.lean:32`, `component_base/metrics/Defs.lean:38` | package `*_init` axioms (uninterpreted) | ii (fixed at allocation) | record only |
| `credsYield` (a connection's per-RPC credentials' metadata) | `grpc/InvGrpc.lean:1585` | `grpc.NewClient.wp_proof` (names-only) | ii | step 3 (it feeds `grpcAttemptMd`; restate as a relation there, or record) |
| `storageSnap`, `walReady`, `walOf` | `storage/InvOpen.lean:60, 71, 93` | bootstrap / `NewStorage` contracts (names-only) | ii | record only |
| `walDirOf` | `storage/WalRecs.lean:181` | bootstrap contracts | ii | record only |
| `snapDBPath`, `dirReadOk` | `snap/Defs.lean:48, 92` | `DBFilePath.wp_proof`, bootstrap contracts (names-only) | ii | record only |
| `mvcc.kvHasherOk` | `mvcc/HashDefs.lean:50` | `newKVHasher`, `WriteKeyValue` (names-only) | ii | record only |
| `reflSliceV` | `Proof/reflect/Values.lean:111` | `reflect.MakeSlice`/`Append` axioms | ii | record only |
| `walGName`, `walRecGName`, `walBaseGName`; `membership.membersOf`; `reflElem`, `reflPtr`, `reflType`, `reflZero`; `msgEncC` | various | — | iii | none |
| **`membership.memBucketsOk`** (cluster `c`'s buckets good, "the local member among them", read off `c.localID`) | `etcdserver/InvRest.lean:625` | the entailment-form axiom `clusterImageOk_restModel.wp_proof` (`Proof/…/membership/clusterImageOk_restModel.lean:26`): `⊢ isRaftCluster c -∗ srvRLogLb γ L' -∗ clusterMem c mem -∗ … ∗ ⌜clusterImageOk c …⌝` | **(i) in form, unverified** | **not in this redesign**: a separate axiom review (Q10) |

The `memBucketsOk` row is the sweep's one candidate of the flawed shape: a pure conclusion about a
pointer-keyed opaque from an entailment. Whether a fresh world can build its left side
(`isRaftCluster c` is a mutex and half points-tos, `srvRLogLb` a ghost lower bound) was not checked, nor
whether its consumer (`RaftCluster.Recover`, names-only) yields a panicking program. Not a finding yet.
Pointer predicates declared as `axiom … : Prop` rather than `opaque` (`grpcPeerOpt`, `grpcSrvOpt`,
`grpcProtoCodec`, `grpcStatsHandlerOk`, `grpcDialOptIs`, `collectorName`) were not classified (Q7).

---

## 2. The new vocabulary

### 2.1 Incoming and outgoing metadata (defined; two opaque leaves)

In `Proof/context/LibKeys.lean` (beside `incomingCtxOk`, which it replaces) and `LibKeysChain.lean`:

```lean
/-- (opaque; TRUSTED; no law) grpc's server transport made the `MD` `v` (a map) holding `f`, with
lower-case keys each with at least one value, and nothing writes it after. -/
opaque metadata.transportMDRaw (v : GoInterface) (f : GoString → Option (List GoString)) : IProp GF
/-- (opaque; TRUSTED; no law) grpc's `metadata` made the `rawMD` `v` (`NewOutgoingContext`,
`AppendToOutgoingContext`) whose `FromOutgoingContext` view is `f`, never written after. -/
opaque metadata.builtRawMDRaw (v : GoInterface) (f : GoString → Option (List GoString)) : IProp GF

/-- what `FromIncomingContext` makes of the value `v` it reads at `mdIncomingKey{}` -/
def metadata.incomingHeld (v : GoInterface) (md : GrpcMd) : IProp GF :=
  (⌜md = none ∧ notMD v⌝) ∨ ∃ f, ⌜md = some f ∧ (∀ k vs, f k = some vs → vs ≠ [])⌝ ∗ □ transportMDRaw v f
/-- **`ctx`'s incoming metadata is `md`** (persistent, per heap): `ctx.Value(mdIncomingKey{})` and
`context.value(ctx, …)` return one `v` (Perennial's chain), and `v` holds `md`. -/
def metadata.incomingIs (ctx : GoInterfaceOk) (md : GrpcMd) : IProp GF :=
  ∃ v, context.ctxValue ctx mdIncomingKeyAny (· = v) ∗ incomingHeld v md
-- outgoingHeld / outgoingIs: the same at mdOutgoingKey{} with builtRawMDRaw (none: not a rawMD)
```

`metadata.incomingCtxOk ctx` becomes `∃ md, incomingIs ctx md` (its WP-form readers get the WP from
`valueAt_of_ctxValue`), `libCtxOk(C)`'s incoming and outgoing parts likewise; `incomingRes`,
`outgoingRes`, `transportMD`, `builtRawMD`, `incomingOf`, `outgoingOf` are deleted.

**Laws (all proved; none trusted).** `incomingIs_cancel` (`ctxField c ↦□ p ∗ incomingIs p md ⊢
incomingIs (*cancelCtx c) md`, from Perennial's `ctxValue_cancel`), `_timer`, `_valueCtx` at another key
(`ctxValue_valueCtx`), `v3rpc.incomingIs_cc` (etcd's wrapper: `isPkgInit context ∗ ccField l ↦□ c ∗
incomingIs c md ⊢ incomingIs (ccCtx l) md`, from `v3rpc.valueAt_cc` and `ctxValue_other`), `_from`
(`ctxValueFrom`), `_raw` (a non-special type from the WP form), and the same for `outgoingIs` (most exist
today for `outgoingCtxOkC`: `LibKeysChain.lean:106-248`). Persistence instances. **No agreement law**:
`incomingIs ctx md1 ∗ incomingIs ctx md2 ⊢ ⌜md1 = md2⌝` is false of a context whose `Value` loops (a
partial-correctness WP satisfies every result), and nothing needs it (Q2).

### 2.2 Errors: one status relation (defined; one opaque leaf)

In `Proof/google_golang_org/grpc/status/StatusRO.lean` and `ErrDesc.lean` (replacing the opaques):

```lean
/-- (opaque; TRUSTED; no law) `s` is a non-nil grpc `*Status` with code `c` and message `m`, never
written after (the producer's guarantee: `grpcStatusRO`'s today). -/
opaque grpcStatusRaw (s : Loc) (c : w32) (m : GoString) : IProp GF
def grpcStatusIs (s : Loc) (c : w32) (m : GoString) : IProp GF := ⌜s ≠ null⌝ ∗ □ grpcStatusRaw s c m
/-- **`status.FromError(err)` gives code `c` and message `m`** (persistent, per heap): `nil` gives `OK`,
`""`; an error without grpc's `GRPCStatus() *Status` gives `Unknown` and the message its `Error()`
stably returns (`errorMsgIs`); one with it, the status its `GRPCStatus()` stably returns. -/
def errStatusIs (err : GoInterface) (c : w32) (m : GoString) : IProp GF :=
  ⌜err = nil ∧ c = OK ∧ m = ""⌝ ∨
  ∃ e, ⌜err = ok e⌝ ∗
    ((⌜noGRPCStatus e.ty ∧ c = Unknown⌝ ∗ errorMsgIs e m) ∨
     (⌜hasGRPCStatus e.ty⌝ ∗ ∃ s, gsReturns e s ∗ grpcStatusIs s c m))
def descIs (err : GoInterface) (m : GoString) : IProp GF := ∃ c, errStatusIs err c m
def codeIs (err : GoInterface) (c : w32) : IProp GF := ∃ m, errStatusIs err c m
```

`errDesc`, `statusCode`, `grpcStatusROP`, `grpcStatusRO` are deleted. `grpcErrMethodsOk` gives `∃ s c m,
gsReturns e s ∗ grpcStatusIs s c m` and, for `Is`, `□ ∀ target m m', descIs (ok e) m -∗ descIs target m'
-∗ WP e.Is(target) {b. ⌜b = true → m = m'⌝}` (pure fact about two parameters fixed before the call).
**Laws (proved):** `descIs_etcdError` (`EtcdError` has no `GRPCStatus`; its translated `Error` returns
`desc`: replaces the axiom `errDesc_etcdError`), `descIs_errorString` (`x.s ↦□ m`), `descIs_ctxErr`
(Part B's `ctxErrIs`), `descIs_deadline`. **No agreement law** (an `Error()` that loops satisfies every
`m`; `notes/fromerror-wand.md`).

### 2.3 Why none of it transfers across heaps

- **crossWorld (a).** No entailment in the redesign concludes a pure fact from `incomingIs`,
  `outgoingIs`, `errStatusIs` or the opaque leaves (I2); the transfer laws conclude relations. So a
  fresh heap with chosen cells gives relations in that heap and nothing in Lean.
- **The persistent-authoritative fresh world (b).** Such a world satisfies `ctxValue` chains of its own
  cells and every WP form (`errorMsgIs`, `gsReturns`, a `Value` WP), so it can build `incomingIs x md`
  for any `x`, `md` (through a WP-form root) — and that is harmless: the only consumers that produce pure
  facts are triples (`FromIncomingContext`, `FromError`, `Code`/`Message`, `errors.Is`, the handler and
  invoker contracts), whose WPs hold vacuously there and are never run. The opaque leaves cannot be built
  there at all (I4: no producer but trusted posts, no law). This is the exact gap that refuted Part A
  (`incomingKept`, a wand from cells to a pure fact); no such wand exists in the new texts (checked
  per text in §3).
- **Adequacy with allocation (c).** Posts of interpreted code (`WithCancel`, `WithTimeout`,
  `newCancellableContext`, `errors.Is`, `fmt.Errorf`) carry relations about allocated values, and pure
  facts only about precondition parameters (`b = true → m = m'`; `pre ++ m` for `ErrorfWrap`). A closed
  run's adequacy gives "for the `m` this run's resources fixed …", which no second run shares; no Lean
  equation about an address remains.
- **Within one run.** Without agreement, two relations of one value never combine; each pure fact is
  produced by one call at the parameter its precondition fixed. In Go terms each relation is true of the
  heap whenever it holds (it is a statement about what `Value`/`Error()`/`GRPCStatus()` return, or a
  producer's guarantee), so each triple is true for every parameter its precondition admits (the
  FromError T8' argument, now uniform).

### 2.4 Probe (de-risk of the shape)

`/shared/tmp/perheap/Probe.lean` (imports `v3rpc/SrvCtxWeakLaws`; checked with `lake --packages=
/shared/tmp/manifest-6d3.json env lean`, no errors, ~13 s): defines `transportMDRawP`, `incomingHeldP`,
`incomingIsP` as in §2.1, and proves **both refuted axioms' replacements as theorems**:
`metadata.incomingIsP_cancel` (6 tactic lines, `ctxValue_cancel`) and `v3rpc.incomingIsP_cc` (14 lines,
`valueAt_cc` + `valueAt_of_ctxValue` + `ctxValue_other`). The errors side was not probed (its definitions
are WP forms already used today: `errorMsgIs`, `grpcErrMethodsOk`'s `GRPCStatus` WP).

---

## 3. Old → new, per trusted text

### 3.1 Incoming metadata

| text | old | new |
|---|---|---|
| `incomingOf_cancelCtx` (+ `_parent_unique`) | axiom, §1.2 | **deleted**; `metadata.incomingIs_cancel` (proved) |
| `v3rpc.incomingOf_cancellableContext` (+ `_field_unique`, `incomingOf_wrapper`) | axiom | **deleted**; `v3rpc.incomingIs_cc` (proved) |
| `FromIncomingContext.spec` | pre `incomingCtxOk ctx`; post on `incomingOf ctx` | `∀ ctx md`, pre `incomingIs ctx md`; post `⌜ok = false ∧ md = none⌝ ∨ ∃ f m, ⌜ok ∧ md = some f ∧ dom m = dom f⌝ ∗ mp ↦$ m ∗ [∗map] …⌜f k = some vs⌝` (facts about the parameter `md`) |
| `context.WithValue.spec` | `⌜incomingOf c' = incomingOf parent⌝` | `□ ∀ md, incomingIs parent md -∗ incomingIs c' md` (a relation transfer in the post of uninterpreted code; true: `valueCtx` at a key not `mdIncomingKey{}` asks its parent) |
| `traceutil.Tracer.Start.spec`, `EnsureTrace.spec` (proved) | `⌜incomingOf ctx' = incomingOf ctx⌝` | `□ ∀ md, incomingIs ctx md -∗ incomingIs ctx' md` |
| `grpcAccepted` (model post) | `▷ Spec (incomingOf ci) m Φ Ψe`; stream `□ Spec (incomingOf ci) γs Dn` | `∃ md, metadata.incomingIs ci md ∗ ▷ Spec md m Φ Ψe` (stream: `∃ md, incomingIs ci md ∗ □ Spec md γs Dn`); the `md` is the one the client's attempt deposited ("The pair") |
| `grpcHandlerOkMd`, `grpcHandlerOwnOkMd`, `grpcMethodOkMd`, `grpcRunOkMd`, `grpcStream{Handler,Method,Run}Ok` | pre `Spec (incomingOf ci) …` | `∀ … md`, pre `incomingIs ci md ∗ Spec md …` |
| `srvStreamInterceptorWOk` | handler gets `⌜incomingOf ci' = incomingOf ci⌝` | handler gets `incomingIs ci' md` (at the stream's `md`) |
| `srvRawStreamIs`, `grpcRunCtx` (via `libCtxOk(C)`) | `∃ v, incomingRes v ∗ ctxValue …` with `transportMD` | `∃ md, incomingIs ci md` (and `outgoingIs ci none`) |
| 16 handler specs (`Spec/…/etcdserverpb/_*_Handler.lean`), 3 `quota*` specs (proved) | as the contracts | as the contracts (mechanical) |
| `auth.ctxTokenOf ctx` (def) | `mdTokenOf (incomingOf ctx)` | **deleted**; `auth.ctxTokenIs ctx tok := ∃ md, incomingIs ctx md ∗ ⌜mdTokenOf md = tok⌝`; consumers quantify `tok` |

How grpc's delivery produces `incomingIs`: `acceptRun`/`acceptRunConns` (model-only, uninterpreted:
`TrustedCode/google_golang_org/grpc.lean`) post `grpcAccepted`, which now carries `incomingIs ci md`
(unfolding to a chain of grpc's `valueCtx` links ending at the `MD` its transport built, plus
`transportMDRaw v f`). True in Go: grpc's HTTP/2 server transport builds `mdata` from the headers and
calls `metadata.NewIncomingContext(s.ctx, mdata)` (= `WithValue(…, mdIncomingKey{}, mdata)`;
`internal/transport/http2_server.go`, `operateHeaders`), and the run context is a `*valueCtx` chain
(`TestRealGrpcTwoStreams`, `examples/axiomcx/incomingof-attack`).

### 3.2 Outgoing metadata

| text | old | new |
|---|---|---|
| `AppendToOutgoingContext.spec` | `⌜outgoingOf c' = mdAdd (outgoingOf ctx) k v⌝`, pre `outgoingCtxOk(C)` | `∀ md`, pre `outgoingIs ctx md`; post `outgoingIs c' (mdAdd md k v)` |
| `withVersion.spec` | `⌜∃ v, outgoingOf c' = mdSet (outgoingOf ctx) … [v]⌝` | pre `outgoingIs ctx md`; post `∃ v, outgoingIs c' (mdSet md "client-api-version" [v])` |
| `streamKeyFromCtx.spec` | `RET #(streamKeyOf (outgoingOf ctx))` | pre `outgoingIs ctx md`; `RET #(streamKeyOf md)` |
| `WithCancelValCtx.spec` (P-i) | `⌜outgoingOf ctx' = outgoingOf inctx⌝` | `□ ∀ md, outgoingIs inctx md -∗ outgoingIs ctx' md` (relation; no pure fact about `ctx'`) |
| `WithTimeoutBackgroundMd.spec` (P-i) | `⌜outgoingOf ctx' = none⌝` | `outgoingIs ctx' none`, **provable** from `ctxValueFrom` + `Background()` (`outgoingCtxOkC_bgFrom` today): the axiom may be deletable (Q6) |
| `grpcAttemptMd conn ctx md`, `grpcInvokerOk` | `mdVals md k = mdVals cm k ++ mdVals (outgoingOf ctx) k` | `grpcAttemptMdOf conn om md` (pure, of a metadata value); `grpcInvokerOk` pre takes `outgoingIs ctx om` and the deposit `▷ ∀ md, ⌜grpcAttemptMdOf conn om md⌝ -∗ Spec md …` |
| `deliversOutgoing c h` (examples auth, in `authkv_bad_unbound`) | `incomingOf h = outgoingOf c` | dropped: the theorem takes `incomingIs h md ∗ ⌜mdVals md "token" = [badToken]⌝` (§4) |

### 3.3 Errors

| text | old | new |
|---|---|---|
| `status.FromError.spec` | `Code()` returns `statusCode err`; `Message()` `errDesc err`; `ok = false → errDesc err = m` | `∀ err c m`, pre `statusErrOk err ∗ errStatusIs err c m`; `Code()` returns `c`, `Message()` returns `m`; T8's `noGRPCStatus → ok = false`; `ok = false → c = Unknown` (all about parameters) |
| `status.Error.spec` | `errDesc err = msg` | post `errStatusIs err c msg` (the `*status.Error` it allocates; uninterpreted) |
| `errors.IsStatusErr.spec` (P-i) | `b = true → errDesc err = errDesc target` (+ T3's type clause) | `∀ err target m m'`, pre `descIs err m ∗ descIs target m'`; post `b = true → m = m'` (+ T3's clause, unchanged: types only) |
| `fmt.ErrorfWrap.spec` (P-i) | `pre <+: errDesc err` | `∀ m`, pre adds `errorMsgIs inner m`; post `descIs err (pre ++ m)` (relation; F1 gone) |
| `grpc.model.respond.spec` | pre `⌜err ≠ nil ∧ errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)` | `∀ … m`, pre `descIs err m ∗ (⌜err ≠ nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m)` (`m` fixed at the call) |
| handler outcome clause (all handler contracts and specs) | `⌜… errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)` | `∃ m, descIs err m ∗ (⌜err ≠ nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m)` |
| `grpcInvokerOk` outcome | `Ψe (errDesc err)` at handler descriptions | `∃ m, descIs err m ∗ (⌜m ∈ handlerDescs⌝ -∗ Ψe m)` |
| `waitRetryBackoff.spec` | `errDesc err ∉ handlerDescs` | `∃ m, descIs err m ∗ ⌜m ∉ handlerDescs⌝` |
| `rpctypes.errDesc_etcdError` | axiom (pure) | **deleted**; `descIs_etcdError` (proved from `EtcdError.Error`'s body) |
| 16 `rpctypes` `Err*_init` axioms | `⌜errDesc e = lit⌝` | `descIs (ok e) lit` (for the `*status.Error`s: `errStatusIs (ok e) code lit`) |
| `errStringToError_init` | `∀ k v, m !! k = some v → errDesc v = k` | `□ ∀ k v, ⌜m !! k = some v⌝ → descIs v k` |
| `toGRPCErrorMap_init` / `grpcErrMapOk` | pure `grpcErrMapOk M kf kc` over `errDesc` of keys and values | `grpcErrMapOk` becomes an `IProp`: `[∗ map] k ↦ v ∈ M, ∃ mk mv, descIs k mk ∗ descIs v mv ∗ ⌜mv = futureRevDesc → k = kf⌝ ∗ … ∗ ⌜mk ∉ readDescs⌝`, plus `descIs kf "mvcc: …future…"`, `descIs kc …`; the cell wand unchanged (no `errDesc`; M4 stays) |
| `grpcErrMethodsOk`, `statusErrOk`, `srvErrOk`, `rpctypesInit` | `grpcStatusRO s (statusCode e)`; `errDesc` | §2.2 forms |
| `isHaltErr.spec`, `leasingKV.acquire` (proved) | `statusCode err` | `codeIs err c` in the pre, `c` in the post |

Every row's (a)/(b)/(c) check: each is a triple, a definition in a triple's pre/post, or a proved law; none
is an entailment with a pure conclusion (I2); every pure post fact is about a parameter fixed in the pre or
a returned value (I3); the opaque leaves (`transportMDRaw`, `builtRawMDRaw`, `grpcStatusRaw`) have no law
(I4). The reviewer should re-run this check on the final Lean texts (Step 7).

---

## 4. Closed and exported statements touched

- **Closed statements (Adequacy/MainLinked): no text change.** Their premises (`ContextReadErrs`, …)
  mention none of the family since Part B. The trust base only shrinks or restates: deleted axioms
  `incomingOf_cancelCtx`, `v3rpc.incomingOf_cancellableContext`, `rpctypes.errDesc_etcdError`, maybe
  `context.WithTimeoutBackgroundMd.wp_proof` (Q6); deleted opaques `incomingOf`, `outgoingOf`, `errDesc`,
  `statusCode`, `grpcStatusROP`, `transportMD`, `builtRawMD` (+ §1.3's); added opaques
  `transportMDRaw`, `builtRawMDRaw`, `grpcStatusRaw` (no laws); ~40 trusted texts restated (§3).
- **Exported statements whose text changes** (listed for approval, Q9):
  - `client_range_any` (`client/v3/Results.lean:2865`) through `rangeErrOut`: `rangeErrΨ … (errDesc err)`
    → `∃ m, descIs err m ∗ rangeErrΨ … m` (the context-error disjunct unchanged). Meaning: "the error's
    description (what `ErrorDesc`/`FromError` return) has the outcome", as before, now per run.
  - `put_end_to_endM`, `deleteRange_end_to_endM`, `range_end_to_endM`, `txn_end_to_endM`,
    `authWrapOut_userAdd` (`v3rpc/Results.lean:392, 442, 492, 554, 862`): `auth.ctxTokenOf ctx` → a
    universally quantified `tok` with the premise `auth.ctxTokenIs ctx tok` (a premise added: the caller
    must hold the context's metadata relation; every caller gets it from grpc's delivery, §3.1). This is a
    new premise on exported (not closed) statements; their closed users discharge it inside the linking
    proofs.
  - `authkv_bad_unbound` (examples auth `Results.lean:123`): premises `deliversOutgoing c h`,
    `mdVals (outgoingOf c) "token" = [badToken]` → `incomingIs h md`, `⌜mdVals md "token" = [badToken]⌝`
    in the entailment's left side.

---

## 5. Go evidence

Behavior the new texts claim, and where it is shown (all at go1.27.3, grpc v1.84.0, the etcd pin):

- `FromIncomingContext(ctx)` reads `ctx.Value(mdIncomingKey{})`, asserts `MD`, copies (grpc
  `metadata/metadata.go:268-282`); `FromOutgoingContext` reads `mdOutgoingKey{}`'s `rawMD`.
- A `*cancelCtx`/`*timerCtx` answers a non-`&cancelCtxKey` key as its parent (go `context.go:442-447,
  776-807`), the `stopCtx` rewrite keeps it, etcd's `cancellableContext` promotes `Value` (fork
  `interceptor.go:270-276`): `examples/axiomcx/incomingof` `TestWrapperInheritsIncoming`,
  `TestIncomingNotConstant`; `examples/axiomcx/incomingof-attack` `TestWrappersNotConstant`,
  `TestAfterFuncer`, `TestAfterFuncerRewrite`, `TestPunning`, `TestRealGrpcTwoStreams` (re-run
  2026-11-18 in this worktree, `GOTOOLCHAIN=go1.27.3 GOWORK=off go test ./...`: both `ok`).
- Status read-only and stable `GRPCStatus()`: `examples/premisefix/grpcstatusro` (cited by
  `grpcStatusRO`'s docstring); `FromError`'s paths: `examples/axiomcx/incomingof-real`
  `TestFromErrorNoGRPCStatus`, `TestCtxErrDescs`; the stability lesson: `examples/axiomcx/fromerrorflip`.
- The transport's `MD` is built once and never written (`operateHeaders`), and grpc's `rawMD` likewise:
  the docstrings of `transportMD`/`builtRawMD` today (`LibKeys.lean:49-70`) carry the citations; Step 1
  adds a Go test that a handler's `FromIncomingContext` copy is independent of the context's map (a write
  to the copy is not seen by a second `FromIncomingContext`), which is what "never written after" needs.
- No new behavior is claimed for `errors.Is`, `fmt.Errorf`, `status.Error`: the new posts say less (a
  relation, or a fact about parameters).

---

## 6. Steps, estimates, checkpoints

Each phase lands on its own (`etc/land.sh` after the coordinator's go), in place (no twin specs: each
opaque is deleted in the phase that replaces it, not kept beside the relation).

| step | what | files (est.) | lines changed (est.) | time |
|---|---|---|---|---|
| 0 | Vocabulary: §2.1/§2.2 definitions, opaque leaves, persistence, transfer laws (incoming, outgoing, errors); the probe's two theorems | 5 | 400 | 2 d |
| 1 | **Incoming**: delete `incomingOf`, the two axioms, `transportMD`, `incomingRes`; FromIncomingContext/WithValue/Tracer.Start/EnsureTrace specs; grpc contracts (`InvGrpc`, `InvGrpcRun`, `InvGrpcStream`); 16+3 handler specs and their proofs; `auth.ctxTokenOf` → `ctxTokenIs` (28 files); server `Hinc` lemmas (`ReqOn`, `ReadWhy`, `LeaseReqOn`, `LeaseCheck`, `EtcdServer__{Put,Txn,LeaseRenew}`); `newStreamInterceptor`; v3rpc Results (5 exported statements) | ~75 | 1500 | 7–9 d |
| — | **Checkpoint C1**: step 1 builds; `tcb-report --check` shows the two axioms gone from the 22 collections; interfaces regenerated; stop for review, then land | | | |
| 2 | **Errors**: delete `errDesc`, `statusCode`, `grpcStatusROP`, `errDesc_etcdError`; FromError/Error/IsStatusErr/ErrorfWrap/respond/waitRetryBackoff; `rpctypes` inits (17), `toGRPCErrorMap_init`; `grpcErrMethodsOk`/`statusErrOk`/`srvErrOk`/`rpctypesInit`; handler outcome clauses; server error path (`ServerKVOn`, `InvKV.grpcErrOut`, `ReadOn.rangeErrDesc`, `mvcc.rangeKeysErr`, `Base.grpcErrMapOk`/`notReadDesc`/`ctxErrDescs`); client (`rpctypes.Error`/`ErrorDesc`, `ContextError`, `isHaltErr`, `isSafeRetry*`, `shouldRefreshToken`, leasing `acquire`, `InvKVConn.ifcErrOut`, `KVService.rangeErrOut`, Results); k8s (`ListDefs`, `listReadError`, kubernetes `Defs`) | ~70 | 2200 | 9–12 d |
| — | **Checkpoint C2a** (inside step 2, first): the server's Range error path (`rangeErrOther_facts`, `rangeErrDesc_of_grpcErrOut`) converted to the ∃-carried form and checked with `lean-check`: the riskiest proof shape (R1). Report before the rest. **C2**: builds; F1 closed; stop, land | | | |
| 3 | **Outgoing**: delete `outgoingOf`, `builtRawMD`, `outgoingRes`; AppendToOutgoingContext/withVersion/streamKeyFromCtx/WithCancelValCtx/WithTimeoutBackgroundMd; `grpcAttemptMd`/`grpcInvokerOk`/`clientAttemptMdOf`; client watch (`InvWatch`, `WatchRecon`, `WatchRun`, `WatchCheck`, `watcher__{Watch,RequestProgress,newWatcherGRPCStream}`, `newWatchClient`: the stream key carried as a record field with `outgoingIs G.ctx G.md`); examples auth (Work*, SetupInv, ClientAuth, `authkv_bad_unbound`) | ~35 | 1200 | 5–7 d |
| — | **Checkpoint C3**: builds; stop, land | | | |
| 4 | The rest of §1.3 as decided (Q7); `notes/axiom-review/perheap.md` (the final texts and the §0 check per text), audit rows, `incomingof-crossworld.md` closed, the `axiom` skill's cross-world paragraph updated with (I1)–(I4) | ~10 | 300 | 2–3 d |

Total: ~190 files touched (100 mention the four directly; the rest through the derived vocabulary and
the contracts), ~5600 lines changed, **5–6.5 weeks** of agent time, against the earlier guess of 2–3 weeks,
which counted `incomingOf` alone (41 files). Each phase needs one or two full builds (the vocabulary
sits under `InvGrpc`/`cache/v3/Base`, which most of the tree imports: `etc/importers.py --count`), in the
build slot.

---

## 7. Risks

- **R1. Proofs that use `errDesc` as a function.** `grpcErrMapOk` (pure facts over pointer keys),
  `rangeErrDesc` (a disjunction on `errDesc err`), `rangeErrOther_facts` and the k8s premises reason by
  rewriting `errDesc` of one value from two sources. Without agreement every such chain must carry the
  `m` from the producer's `∃ m` to the consumer's call. Expected to work (each consumer is a Go call
  whose precondition can fix `m`), but the cost may exceed the estimate; C2a measures it first.
- **R2. A proof needs agreement after all** (two relations of one value, no call between). Then stop: an
  agreement law is a new trusted entailment with a pure conclusion and would need its own review (only
  sound over an opaque leaf with a ghost-map model, never over a WP form).
- **R3. Build cost and memory.** Changing `LibKeys`/`InvGrpc`/`cache/v3/Base` rebuilds most of the tree
  (~12k modules) per phase; `[∗list]` over `List.replicate` contexts in big proofs must be framed
  explicitly (CLAUDE.md, "Large contexts").
- **R4. Meaning of the restated exported statements.** "∃ m, descIs err m ∗ P m" is partial-correctness:
  for an error whose `Error()` loops, any `m` works — but then nothing that reads the description
  returns. A reviewer may prefer to see it stated in the docstrings of `rangeErrOut` and the handler
  contracts (planned).
- **R5. The secondary family** (§1.3) may hold items whose fix is larger than a rename; Q7 keeps them out
  of the first three phases unless they are exposed.
- **R6. Interference with other sessions.** The grpc contracts and `cache/v3/Base` are shared by most
  slices: each phase lands quickly after its checkpoint, merging `lean` first.

---

## 8. Open questions (each with a recommendation)

- **Q1. Order and granularity.** Recommend **incoming first** (step 1) (removes the two refuted axioms from 22
  collections; ~1.5 weeks), then **errors** (closes F1 and the (c)-exposed posts), then **outgoing**, then
  the secondary family; each phase landed separately.
- **Q2. Agreement laws.** Recommend **none** in the design (§2.1, §2.2); any proof that needs one stops
  for review (R2).
- **Q3. `incomingIs` defined or opaque.** Recommend **defined** over Perennial's `ctxValue` chain (the
  probe proves both former axioms), with the opaque only at the `MD` leaf (`transportMDRaw`).
- **Q4. One error relation.** Recommend `errStatusIs err c m` as the one primitive, with `descIs`/`codeIs`
  its projections (one producer obligation, `FromError` stated once).
- **Q5. `rpctypes.errDesc_etcdError`.** Recommend **delete** (a proved `descIs_etcdError`).
- **Q6. `WithTimeoutBackgroundMd`.** Recommend deriving its outgoing conjunct (and, if Perennial's proved
  `WithTimeout` gives the rest, deleting the axiom) in step 3; otherwise restate as in §3.2.
- **Q7. The secondary family.** Recommend: in step 4 replace the three library-key leaves that sit beside
  `transportMD` in `libCtxOk` (`transportPeer`, `otelSpan`, `builtTrace`: opaque `Prop` → opaque raw
  `IProp`, the same mechanical change); record the other per-run-only ones (verdict (ii): `vecLabels`, the
  WAL/snap/storage contract leaves, `kvHasherOk`, `reflSliceV`) in `notes/axiom-review/perheap.md` with the
  (I1)–(I4) remedy, each a later item; classify the `axiom … : Prop` pointer predicates there too. The one
  (i) candidate is Q10.
- **Q8. F1 (`ErrorfWrap`, `IsStatusErr`).** Recommend an audit row and a bug record now
  (`notes/errorfwrap-adequacy.md`, "fixed by the per-heap redesign, step 2"), no separate hot fix: a
  hot fix would restate the same two specs twice.
- **Q9. The exported statements' text changes** (§4): recommend approving as listed; the new `tok`
  premise of v3rpc's five `*_end_to_endM`/`authWrapOut_userAdd` is discharged by every caller from grpc's
  delivery.
- **Q10. `membership.memBucketsOk`** (§1.3). Recommend a short `axiom`-skill review of
  `clusterImageOk_restModel.wp_proof` with the cross-world and persistent-authoritative checks, outside this
  redesign (it is not about metadata or errors), before step 4.
