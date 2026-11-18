# Scope: the per-heap redesign — pointer-keyed pure functions become per-run Iris relations

**Status: SCOPE, revision 2 (after independent review 1, `/shared/tmp/perheap/review-1.md`), for a second
independent review, then the user (hard stop). No Lean changed in the tree.** Approved to be written
by the user 2026-11-18 via etcd-grove-03. Revision 2 answers every item of review 1 (§9 maps each item to
its answer); revision 1 is commit `dda8f5f7d8`. Branch `perheap-scope` off `lean` `49bd7924e6` (worktree
`/shared/etcd-grove-incomingof`), the perheap agent of etcd-grove-03. Background: `notes/axiom-review/
ctx-descs.md`, `notes/axiom-review/incomingof.md` (Part A refuted), `notes/axiom-review/incomingof-b.md`
(Part B, T1–T8'), `notes/incomingof-crossworld.md`, `notes/fromerror-wand.md`, `notes/incomingof-scope.md`
(§0, A-D, Q1). Lean probes (throwaway, not in the tree), checked with `lake env lean` at this head, no errors: the
incoming side `/shared/tmp/perheap/Probe.lean`, the errors side `/shared/tmp/perheap/ProbeErr.lean` (§2.4).

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
> its conclusions are relations again (transfer laws), and each transfer law is *proved* where the
> relation is defined, or is in the post of a call to uninterpreted code (`WithValue`, `Tracer.Start`:
> review 1, m2).
> **(I3)** A pure fact about `a` comes only from a triple whose precondition holds `R x a` with `a` fixed
> before the call (the fromerror-wand lesson), and is about `a` and the call's results; never a wand in a
> post that takes `R x a'` later.
> **(I4)** The only opaque leaves are `IProp`s made by trusted producers (posts of uninterpreted calls),
> with **no law** (no agreement, no transfer), so no proof and no fresh world can build or combine them.
> **(I4')** No post of code with Lean semantics (translated, or a Perennial model with an `impl`)
> produces a leaf, and every leaf takes the heap's names (`[hG : HeapGS _ GF]`) in its binders, so that
> its intended model may sit at the run's ghost names (review 1, m1: the revision-1 probe's leaf was
> `hG`-free, so a leaf made inside a nested interpreted run would be the real run's leaf). Checked per
> text in Step 4 (`notes/axiom-review/perheap.md`).
> **(I5)** A pure fact a producer gives about a *pointer-free* value (an `rpctypes.EtcdError` struct, a
> metadata map value `GrpcMd`, a code) is allowed (it is the same in every heap); the value pin of
> `descIs` (§2.2) is one.

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
a fact. Review 1 (§5) confirms F1 and that it is a Lean-level defect today; revision 2 proposes a
separate early hot fix, **H0** (§5a), which can land before the redesign (Q8). `errors.IsStatusErr`'s
current text (`b = true → errDesc err = errDesc target`) is not exposed on its own: its identity case is
`errDesc e = errDesc e`, its `Is`-method case is what `statusErrOk`'s `Is` clause (a premise the producer
proves) already says, and once H0 is in no other post of interpreted code fixes an `errDesc` value, so
equalities alone are satisfiable (a constant `errDesc`). B1 (§2.2) is a defect of revision 1's
*proposed* text, not of the current one. Not yet in `notes/audit.md` (H0 adds the row).

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

### 1.2a What revision 1's inventory missed (review 1, §1)

Counts by `grep -rlE` over `Proof/` and `Spec/` at `49bd7924e6` (files; a file can be in several rows):

| vocabulary | files | how it moves |
|---|---|---|
| `auth.ctxTokenOf` and the predicates built on it: `auth.ctxBound` (`server/v3/auth/InvAuth.lean:767`, the post of `AuthInfoFromCtx`), `principalBound` (`etcdserver/AuthBound.lean`), `noPrincipalFrom`, `tokRefusedFrom` (`auth/WhyDefs.lean`), `userAttemptOk` (examples auth `ClientAuth.lean:92`) | 38 | re-indexed by the token (`Option GoString`), not the context (§3.1, M1); checkpoint C1a |
| specs taking `metadata.incomingCtxOk` (`AuthInfoFromCtx`, `AuthInfoFromTLS` `Spec/…/auth/authStore__AuthInfoFromCtx.lean:25`, `FreshCtx.lean:53`, `FromIncomingWeak.lean:31`) and `ReadWhy.lean:190,201` (lemmas with `incomingOf c = incomingOf c'` as a hypothesis) | 9 | `∀ md`, pre `ctxInMD ctx md` (§3.1) |
| `context.libCtxOk` (its incoming part; the server's `etcdserver/Results.lean:657,719,780,825` take it) | 81 | the incoming part leaves `libCtxOk` (M2, §3.1); most files only rebuild |
| `srvRawStreamIs`, `grpcRunCtx` | 44 | likewise (M2) |
| the outgoing family `outgoingCtxOk`, `outgoingCtxOkC`, `builtRawMD` (88 for `outgoingCtxOkC` alone in review 1's count; 110 now; ~65 `Spec/` files: leasing, concurrency, election, lock, cache, k8s watch, `WithRequireLeader.spec`) | 115 | `outgoingCtxOkC ctx` keeps its name and arity, redefined as `∃ md, outMD ctx md` (§3.2): most files only rebuild; text edits where `outgoingOf` is named (31 files) |
| `statusErrOk`, `srvErrOk`, `grpcErrMethodsOk` (definitions change, names kept) | 198 | rebuild; text edits only where the old `grpcStatusRO`/`errDesc` is unfolded |
| k8s `ListDefs.listErrF`/`kClientErr`, `readErrIs`; client `rangeErrOut`, `rangeErrSound`, `isSafeRetry*`, `shouldRefreshToken`, `rpctypes.Error` | (in the 100) | restated, not converted (M1; §3.3) |
| `status.Code.wp_proof` (`Proof/google_golang_org/grpc/status/Code.lean:27`, post `True`) | 1 | its premise `statusErrOk` changes meaning only |
| **`SpecPlan/`** (`errView`/`statusErr`/`errMsg`/`plainErr`/`statusAt`/`sentStatus`/`outMD`, `SpecPlan/Spec/google_golang_org/grpc/Api.lean:246-290`; `ctxInMD`, `ctxInMD_agree.spec`, `Api.lean:463, 922-925`; `ctxTokenMd`, `SpecPlan/Spec/go_etcd_io/etcd/client/v3/Api.lean:609`; 14 files use `errView`/`ctxInMD`; 3 mention `errDesc` in prose) | 14 | converge (§2.0); two ledger entries (`notes/specs-only/ledger.md`, 2026-11-18, Pending) |

Union of every name above and the four: **362 files** mention one; of them ~190 need text edits (the rest
rebuild because a definition under a kept name changes). No mention in `GooseLang/`, `TrustedCode/`,
`RaftWitness/`, `RaftTla/`, `PorcupineDag/`, `WalTester/` (review 1 confirms).

### 1.3 The rest of the family

Every other `opaque` to a pure type whose argument holds a `Loc`, a `GoInterface` or a pointer-carrying
value was classified (read-only sweep by a subagent, 2026-11-18; spot-checked). Verdicts: **(i)** same
flaw (a trusted entailment, or a post of interpreted code, concludes the pure fact); **(ii)** per-run only
(heap-dependent, given only by posts of uninterpreted calls: sound per execution, not in Iris's model);
**(iii)** not of the family (identity- or type-keyed, or a function of pure data).

| opaque | declared | trusted sources of its pure fact | verdict | in the redesign |
|---|---|---|---|---|
| `grpcStatusROP` (`*Status` read-only with code `c`) | `grpc/status/StatusRO.lean:27` | `status.Error`, `ErrGRPC*_init`, `toGRPCErrorMap_init`, grpc model posts, inside `grpcErrMethodsOk` | ii | **replaced** (`status.statusAt`, step 2) |
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

### 2.0 Convergence with `SpecPlan/` (review 1, (1) MAJOR)

CLAUDE.md ("The spec plan and convergence"): a reworked spec takes `SpecPlan/`'s statement unless the proof
shows it wrong, and a divergence goes in the ledger first. `SpecPlan/` already has per-run `IProp` vocabulary
for this redesign (`SpecPlan/Spec/google_golang_org/grpc/Api.lean`); revision 2 **adopts its names and
split** and records the two places where it must differ (ledger, 2026-11-18, two entries, Pending):

| SpecPlan | here | realization | difference |
|---|---|---|---|
| `ctxInMD ctx o` (`Api.lean:463`) | `metadata.ctxInMD` (was `incomingIs`) | defined, §2.1 | **no** `ctxInMD_agree` (ledger entry 1, §2.3a) |
| `outMD ctx md` (`Api.lean:290`) | `metadata.outMD` (was `outgoingIs`) | defined, §2.1 | `Option`: `none` for a context with no outgoing metadata (SpecPlan's `md : MD` reads `none` as the empty map; the proofs distinguish them today, `outgoingOf ctx = none`) |
| `statusAt s c m` (`Api.lean:263`) | `status.statusAt` (was `grpcStatusRaw`/`grpcStatusIs`) | opaque leaf (with `s ≠ null`) | none (SpecPlan's `nil` = `OK` case is a definition over it) |
| `errMsg err m` (`Api.lean:252`) | `errMsg` (on `GoInterface`) | defined: `∃ e, err = ok e ∗ errorMsgIs e m` | none |
| `plainErr err` (`Api.lean:256`) | `plainErr` | defined: no `GRPCStatus` method on `err` nor on any error its `Unwrap` chain reaches (for the leaf errors `statusErrOk` admits: no `GRPCStatus` method) | none |
| `statusErr err c m` (`Api.lean:248`) | `statusErr` | defined: `GRPCStatus` method that stably returns `s` with `statusAt s c m` | none |
| `errView err c m ok` (`Api.lean:266`) | `errView`, `FromError`'s pre | as SpecPlan's | none |
| — | **`descIs err m`** (message only), with the value pin (§2.2) | defined | new (ledger entry 2): `errView` has no case for an error *wrapping* a status error (grpc v1.84.0 `status/status.go:112-125`: the wrapped code, message `err.Error()`), and the server's and client's description reasoning needs the message without the code |
| `ctxTokenMd ctx tok` (client `Api.lean:609`) | `ctxTokenMd` (outgoing, examples auth) | `∃ md, outMD ctx (some md) ∗ ⌜mdVals md "token" = [tok]⌝` | none |

### 2.1 Incoming and outgoing metadata (defined; two opaque leaves)

In `Proof/context/LibKeys.lean` (beside `incomingCtxOk`, which it replaces) and `LibKeysChain.lean`:

```lean
/-- (opaque; TRUSTED; no law) grpc's server transport made the `MD` `v` (a map) holding `f`, with
lower-case keys each with at least one value, and nothing writes it after: grpc writes it once in
`operateHeaders`, and passes it to a user `InTapHandle` after `NewIncomingContext`
(`internal/transport/http2_server.go:543-575`); etcd's server installs none (no `InTapHandle` in etcd
server v3.7.x), a configuration fact the Step 1 Go test checks (review 1, m3). -/
opaque metadata.transportMDRaw [hG : HeapGS _ GF] (v : GoInterface) (f : GoString → Option (List GoString)) : IProp GF
/-- (opaque; TRUSTED; no law) grpc's `metadata` made the `rawMD` `v` (`NewOutgoingContext`,
`AppendToOutgoingContext`) whose `FromOutgoingContext` view is `f`, never written after. -/
opaque metadata.builtRawMDRaw [hG : HeapGS _ GF] (v : GoInterface) (f : GoString → Option (List GoString)) : IProp GF

def metadata.incomingHeld (v : GoInterface) (md : GrpcMd) : IProp GF :=
  (⌜md = none ∧ notMD v⌝) ∨ ∃ f, ⌜md = some f ∧ (∀ k vs, f k = some vs → vs ≠ [])⌝ ∗ □ transportMDRaw v f
/-- **`ctx`'s incoming metadata is `md`** (persistent, per heap): `ctx.Value(mdIncomingKey{})` returns
`v` (Perennial's chain) and `v` holds `md`. -/
def metadata.ctxInMD (ctx : GoInterfaceOk) (md : GrpcMd) : IProp GF :=
  ∃ v, context.ctxValue ctx mdIncomingKeyAny (· = v) ∗ incomingHeld v md
-- outgoingHeld / outMD: the same at mdOutgoingKey{} with builtRawMDRaw (none: not a rawMD)
```

`metadata.incomingCtxOk ctx` is deleted (its users take `ctxInMD ctx md` with `md` a parameter);
`incomingRes`, `outgoingRes`, `transportMD`, `builtRawMD`, `incomingOf`, `outgoingOf` are deleted.
`outgoingCtxOkC ctx` keeps its name, redefined as `∃ md, outMD ctx md` (its 110 files rebuild; only those
naming `outgoingOf` change text).

**Laws (all proved; none trusted).** `ctxInMD_cancel` (`ctxField c ↦□ p ∗ ctxInMD p md ⊢ ctxInMD
(*cancelCtx c) md`, from Perennial's `ctxValue_cancel`: probe), `_timer`, `_valueCtx` at another key,
`v3rpc.ctxInMD_cc` (etcd's wrapper: probe), `_from` (`ctxValueFrom`), `_background` (`none`), and the same
for `outMD` (most exist for `outgoingCtxOkC`: `LibKeysChain.lean:106-248`). Persistence instances.
**No `_raw` law** (no `ctxInMD` from a `Value` WP form of a user context type): a run's context's root is
grpc's (`grpcAccepted`, M2). **No agreement law** (§2.3a).

### 2.2 Errors (defined; one opaque leaf)

```lean
/-- (opaque; TRUSTED; no law) `s` is a non-nil grpc `*Status` with code `c` and message `m`, never
written after (the producer's guarantee; `grpcStatusRO`'s today, `examples/premisefix/grpcstatusro`). -/
opaque status.statusAt [hG : HeapGS _ GF] (s : Loc) (c : w32) (m : GoString) : IProp GF
def statusErr (err) (c) (m) := ∃ e s, ⌜err = ok e ∧ GRPCStatus ∈ e.ty⌝ ∗ gsReturns e s ∗ ⌜s ≠ null⌝ ∗ □ statusAt s c m
def errMsg (err) (m) := ∃ e, ⌜err = ok e⌝ ∗ errorMsgIs e m
def plainErr (err) : Prop := ∀ e, err = ok e → GRPCStatus ∉ e.ty ∧ isLeafError e   -- the leaf errors statusErrOk admits
/-- **What `status.FromError` sees of `err`** (SpecPlan's). -/
def errView (err) (c) (m) (ok : Bool) :=
  (⌜ok⌝ ∗ statusErr err c m) ∨ (⌜¬ok ∧ c = Unknown ∧ plainErr err⌝ ∗ errMsg err m) ∨ ⌜err = nil ∧ ok ∧ c = OK ∧ m = ""⌝
/-- **`err`'s description is `m`**: what `rpctypes.ErrorDesc`/`FromError(err).Message()` returns (for an
error without `GRPCStatus`, wrapping or not, its `Error()`; with it, the status's message), plus the
**value pin**: of an `EtcdError` value, `m` is its `desc`. -/
def descIs (err) (m) :=
  (⌜err = nil ∧ m = ""⌝ ∨ (∃ e, ⌜err = ok e ∧ GRPCStatus ∉ e.ty⌝ ∗ errorMsgIs e m) ∨ ∃ c, statusErr err c m) ∗
  ⌜∀ y : EtcdError, err = mkOk EtcdError.ty #y → m = y.desc⌝
```

`errDesc`, `statusCode`, `grpcStatusROP`, `grpcStatusRO` are deleted. `grpcErrMethodsOk` gives `statusErr`
for its `GRPCStatus` clause and, for `Is`, `□ ∀ target m m', descIs (ok e) m -∗ descIs target m' -∗ WP
e.Is(target) {b. ⌜b = true → m = m'⌝}` (a user `Is` method: the producer's obligation; `*status.Error.Is`
compares the two statuses' messages, `internal/status/status.go:222-228`).

- **Why the pin (review 1, M1).** Without agreement, `err = target` (B1's identity branch) gives nothing
  about the `m` a producer fixed for `err`. Every error value the chains compare by identity is an
  `EtcdError` *value* (`rpctypes`' `ErrFutureRev`, `ErrUserEmpty`, `ErrInvalidAuthToken`,
  `ErrAuthOldRevision`, `ErrNoLeader`, …: pointer-free structs), and for those the pin turns identity into
  equal descriptions with no agreement law: `err = mkOk #x` and the pin give `m = x.desc`. The pin is a pure
  fact of a pointer-free value (I5), true in Go (`EtcdError.Error` returns `e.desc`, translated and proved:
  `rpctypes.EtcdError.Error.wp_proof`), and every producer proves it: the law below for `EtcdError`
  values, and vacuously (by type) for everything else (a `*status.Error`, a `*fmt.wrapError`, an
  `*errorString`, a context error).
- **Laws (proved):** `descIs_etcdError : ⊢ descIs (mkOk EtcdError.ty #x) x.desc` (replaces the axiom
  `rpctypes.errDesc_etcdError`; **proved in the probe** from `EtcdError.Error`'s proved spec, with
  `go.IntoValInj EtcdError`: a two-field struct, derivable from `go.BasicIntoValInj` as
  `k8s …/consistency/Defs.lean:181-209` does; Step 0), `descIs_errorString` (`errStrCell x m`),
  `descIs_ctxErr` (Part B's `ctxErrIs`), `descIs_of_errView` (when `ok = false` or `nil`),
  `errorfWrap_descIs` (B2, below: **proved in the probe**). **No agreement law.**
- **`errView` for leaf errors only (review 1, m4).** The no-`GRPCStatus` case of `errView` requires
  `plainErr` (code `Unknown` is false of an error wrapping a status error: `FromError` returns the wrapped
  code); `descIs` keeps the message case without `plainErr` (the message *is* `err.Error()` there).
- **Incompleteness, not unsoundness (review 1, m5).** A type whose `GRPCStatus()` returns `nil`
  (`status.go:103-108`: `Unknown`, `err.Error()`) satisfies no case of `errView`/`descIs`; no producer
  makes one. Stated in the docstrings.

### 2.3 Why none of it transfers across heaps

- **crossWorld (a).** No entailment in the redesign concludes a pure fact from `ctxInMD`, `outMD`,
  `descIs`, `errView` or a leaf (I2); the transfer laws conclude relations. The value pin is a pure fact
  *inside* `descIs`, about a pointer-free value: a fresh heap can build `descIs` only through a producer
  that proves the pin, which holds of the value in every heap.
- **The persistent-authoritative fresh world (b).** It can build WP forms (`errorMsgIs`, a `GRPCStatus`
  WP), so it builds `descIs x m` for an error with no `GRPCStatus` method and a looping `Error()`, for
  every `m`. Harmless: the pure facts sit in triple posts (`FromError`, `errors.Is`, the handler and invoker
  contracts), vacuous in such a world. It cannot build `transportMDRaw`/`builtRawMDRaw`/`statusAt` (I4), nor
  `ctxInMD` (no `_raw` law: its only root is the leaf; `ctxInMD x none` needs `ctxValue`'s chain to end at
  `Background()`), so it builds no run context.
- **Adequacy with allocation (c).** Posts of interpreted code (`WithCancel`, `WithTimeout`,
  `newCancellableContext`, `errors.Is`, `fmt.Errorf`) carry relations about allocated values and pure facts
  only about precondition parameters (`b = true → err = target ∨ m = m'`) or pointer-free values; no leaf
  (I4'). A closed run's adequacy gives facts about its own parameters; no Lean equation about an address
  remains.
- **Within one run.** Each pure fact is produced by one call at the parameters its precondition fixed:
  `FromError` reads `GRPCStatus()`/`Error()` *during* the call (grpc `status/status.go:96-127`), so its
  post is true for every `(c, m)` its pre admits (the T8' argument); `errors.Is` is B1's restatement,
  true in Go branch by branch (identity: go1.27.3 `src/errors/wrap.go:54-57`; `*status.Error.Is`; a user
  `Is` method: the producer's obligation).

### 2.3a Agreement: why not SpecPlan's `ctxInMD_agree` (ledger entry 1)

`ctxInMD_agree.spec` (`ctxInMD ctx o ∗ ctxInMD ctx o' ⊢ ⌜o = o'⌝`) is an entailment with a pure conclusion
over a per-heap relation. Its soundness depends on the realization, which SpecPlan leaves open:

- **With this Scope's realization (defined over Perennial's `ctxValue`), it is false.** `ctxValue` has a
  case for a context type that is not one of `context`'s own (a `Value` WP form); a partial-correctness WP of
  a `Value` that loops satisfies every result, so `ctxInMD ctx o` holds for every `o`. Dropping that case
  (no `_raw` law, §2.1) removes the producer but not the issue for the *derived* chains: `ctxValue`'s
  `valueCtx` case delegates every other key to its parent's `Value`, again a WP form.
- **As an opaque with trusted transfer entailments (SpecPlan's shape), it needs all of:** leaves indexed by
  `hG` (otherwise attack (b) crosses worlds: `ctxField c ↦□ p` in a fresh heap of one's choice, with real
  `ctxInMD p o1` and `ctxInMD p' o2`, gives `ctxInMD (*cancelCtx c) o1` and `… o2`, which agreement joins:
  review 1's m1 shape); producers only along chains of `context`'s own types and etcd's wrapper, whose
  fields Go never writes after construction; transfers *assumed* (they could not be proved from
  `ctxValue`, whose WP-form cases defeat agreement); and an intended model (a ghost map from contexts to
  metadata, whose consistency rests on the chains' immutability). That is two more trusted entailments
  (the refuted pair's relational versions) and a model argument, to buy one law.
- **Nothing needs it.** The two consumers that seemed to (review 1: `authkv_bad_unbound`/`ctxBound`, and
  `newStreamInterceptor`) are restated with one `md` carried from one producer (M1's re-indexing, M2's single
  source; §3.1). Every other `incomingOf` rewrite in the tree is a transfer (`incomingOf ctx' = incomingOf
  ctx`), which the proved transfer laws replace.

Recommendation (Q2): no agreement law; ledger entry 1 proposes deleting `ctxInMD_agree.spec` from
`SpecPlan/` (and `ctxPeerCN`'s half with it, for the same reason: `peer.FromContext` reads through the same
`Value` chain), with this argument as evidence; Pending the user's decision.

### 2.4 Probes (de-risk of the shape)

Both throwaway, not in the tree, checked with `cd /shared/etcd-grove-incomingof && lake
--packages=/shared/tmp/manifest-6d3.json env lean <file>` at `49bd7924e6`, no errors, no `sorry`:

- `/shared/tmp/perheap/Probe.lean` (incoming, revision 1): `incomingIsP` (= `ctxInMD`) defined as §2.1;
  **both refuted axioms' replacements are theorems**: `metadata.incomingIsP_cancel` (6 lines,
  `ctxValue_cancel`), `v3rpc.incomingIsP_cc` (14 lines, `valueAt_cc` + `valueAt_of_ctxValue` +
  `ctxValue_other`). (Its leaf is `hG`-free; Step 0 declares the leaves with `hG`, I4'.)
- `/shared/tmp/perheap/ProbeErr.lean` (errors, revision 2, ~170 lines): `descIsP` as §2.2 with the value
  pin over an opaque `grpcStatusRawP`;
  - `descIsP_etcdError` (**the axiom `errDesc_etcdError` becomes a theorem**, 20 lines, from
    `rpctypes.EtcdError.Error.spec` and `go.IntoValInj EtcdError`);
  - `errorfWrap_descIsP` (**B2: `fmt.errorfWrapIs ii inner pre ⊢ ∃ s, descIsP (ok ii) (pre ++ s)`**, both
    disjuncts, from `ErrorStringLeaf` and `EtcdError`'s leaf fact; nothing new trusted);
  - `IsStatusErrP.spec`: **B1's restated `errors.IsStatusErr`** (post `b = true → (err = target ∨ m = m')
    ∧ T3`);
  - `listRead_step`: **M1's k8s chain closes without agreement**: the triple of `errors.Is(err,
    ErrFutureRev)` under `readErrIs`'s restated pre (`∃ m, statusErrOk err ∗ descIsP err m ∗ □(⌜m =
    futureRevDesc⌝ -∗ ⌜T3⌝ -∗ □ Qf)`) gives `b = true → Qf`, both branches of B1 (identity through the
    pin, equal descriptions directly).

  Not probed: `statusErrOk` is today's (its `Is` clause still names `errDesc`; Step 0 restates it as
  above); `shouldRefreshToken` (the same shape as `listRead_step`, §3.3).

---

## 3. Old → new, per trusted text

### 3.1 Incoming metadata

| text | old | new |
|---|---|---|
| `incomingOf_cancelCtx` (+ `_parent_unique`) | axiom | **deleted**; `metadata.ctxInMD_cancel` (proved) |
| `v3rpc.incomingOf_cancellableContext` (+ `_field_unique`, `incomingOf_wrapper`) | axiom | **deleted**; `v3rpc.ctxInMD_cc` (proved) |
| `FromIncomingContext.spec` | pre `incomingCtxOk ctx`; post on `incomingOf ctx` | `∀ ctx md`, pre `ctxInMD ctx md`; post `⌜ok = false ∧ md = none⌝ ∨ ∃ f m, ⌜ok ∧ md = some f ∧ dom m = dom f⌝ ∗ mp ↦$ m ∗ [∗map] …` (facts about the parameter `md`) |
| `context.WithValue.spec` | `⌜incomingOf c' = incomingOf parent⌝` | `□ ∀ md, ctxInMD parent md -∗ ctxInMD c' md` (transfer in the post of uninterpreted code, m2) |
| `traceutil.Tracer.Start.spec`, `EnsureTrace.spec` (proved) | `⌜incomingOf ctx' = incomingOf ctx⌝` | `□ ∀ md, ctxInMD ctx md -∗ ctxInMD ctx' md` |
| `grpcAccepted` (model post; **the single source**, M2) | `▷ Spec (incomingOf ci) m Φ Ψe`; stream `□ Spec (incomingOf ci) γs Dn` | `∃ md, ctxInMD ci md ∗ ▷ Spec md m Φ Ψe` (stream: `∃ md, ctxInMD ci md ∗ □ Spec md γs Dn`); the `md` is the one the client's attempt deposited |
| `grpcRunCtx`, `context.libCtxOk(C)`, `srvRawStreamIs` (M2) | incoming part `∃ v, incomingRes v ∗ ctxValue …` | **incoming part removed**: they keep the library keys' other facts (outgoing `none` for a run context, peer, span, trace); a run context's `ctxInMD` comes only from `grpcAccepted`. `etcdserver/Results.lean:657,719,780,825` take `libCtxOk ctx`: meaning weakens (one fact fewer), text unchanged |
| `grpcHandlerOkMd`, `grpcHandlerOwnOkMd`, `grpcMethodOkMd`, `grpcRunOkMd`, `grpcStream{Handler,Method,Run}Ok`, `srvInterceptorOk` | pre `Spec (incomingOf ci) …` | `∀ … md`, pre `ctxInMD ci md ∗ Spec md …` |
| `srvStreamInterceptorWOk` (M2; `newStreamInterceptor.lean:220, 264-268`) | handler gets `⌜incomingOf ci' = incomingOf ci⌝`; interceptor reads `incomingCtxOk` from `libCtxOk_of_runCtx` | the interceptor **receives** the stream's `ctxInMD ci md` in its contract and reads with it (`FromIncomingContext` at that `md`), and passes `ctxInMD ci' md` to the handler; one `md` from `grpcAccepted` to the handler |
| 16 handler specs, 3 `quota*` specs (proved) | as the contracts | as the contracts |
| `auth.ctxTokenOf ctx` (def) | `mdTokenOf (incomingOf ctx)` | **deleted**; `auth.ctxTokenIs ctx tok := ∃ md, ctxInMD ctx md ∗ ⌜mdTokenOf md = tok⌝` (for statements); proofs carry `md` |
| `auth.ctxBound M ctx a` (+ `principalBound`, `noPrincipalFrom`, `tokRefusedFrom`, `userAttemptOk`; M1) | indexed by the context, through `ctxTokenOf` | **indexed by the token**: `ctxBound M (tok : Option GoString) a := ⌜a = null⌝ ∨ ∃ t, ⌜tok = some t⌝ ∗ infoBound M t a`; likewise the others |
| `authStore.AuthInfoFromCtx.spec`, `AuthInfoFromTLS.spec` (M1) | pre `incomingCtxOk ctx`; post `ctxBound M ctx a` | `∀ md`, pre `ctxInMD ctx md`; post `ctxBound M (mdTokenOf md) a` |

**Checkpoint C1a** (M1, inside step 1, first): the chain from `AuthInfoFromCtx` through `ctxBound` and
`principalBound` to the handler's `tok` (`EtcdServer__{Put,Range,Txn}` auth paths, `ReqOn`, `ReadWhy`),
converted and checked with `lean-check`, before the rest of step 1.

How grpc's delivery produces `ctxInMD`: `acceptRun`/`acceptRunConns` (model-only, uninterpreted) post
`grpcAccepted`. True in Go: grpc's HTTP/2 server transport builds `mdata` from the headers and calls
`metadata.NewIncomingContext(s.ctx, mdata)` (`operateHeaders`), and the run context is a `*valueCtx` chain
(`TestRealGrpcTwoStreams`, `examples/axiomcx/incomingof-attack`).

### 3.2 Outgoing metadata

| text | old | new |
|---|---|---|
| `AppendToOutgoingContext.spec` | `⌜outgoingOf c' = mdAdd (outgoingOf ctx) k v⌝` | `∀ md`, pre `outMD ctx md`; post `outMD c' (mdAdd md k v)` |
| `withVersion.spec` | `⌜∃ v, outgoingOf c' = mdSet …⌝` | pre `outMD ctx md`; post `∃ v, outMD c' (mdSet md "client-api-version" [v])` |
| `streamKeyFromCtx.spec` | `RET #(streamKeyOf (outgoingOf ctx))` | pre `outMD ctx md`; `RET #(streamKeyOf md)` |
| `WithCancelValCtx.spec` (P-i) | axiom, `⌜outgoingOf ctx' = outgoingOf inctx⌝` | **a corollary** (m6): `□ ∀ md, outMD inctx md -∗ outMD ctx' md`, proved from `WithCancel`'s proved spec and `ctxValue_cancel`; the axiom goes |
| `WithTimeoutBackgroundMd.spec` (P-i) | axiom, `⌜outgoingOf ctx' = none⌝` | **a corollary** (Q6): `outMD ctx' none` from `ctxValueFrom` + `Background()`; the axiom goes if Perennial's proved `WithTimeout` gives the rest (else restated) |
| `grpcAttemptMd`, `grpcInvokerOk`, `credsYield` | `mdVals md k = mdVals cm k ++ mdVals (outgoingOf ctx) k` | `grpcAttemptMdOf conn om md` (pure, of metadata values); pre `outMD ctx om` and the deposit `▷ ∀ md, ⌜grpcAttemptMdOf conn om md⌝ -∗ Spec md …` |
| `deliversOutgoing c h` (examples auth) | `incomingOf h = outgoingOf c` | dropped (§4) |

### 3.3 Errors

| text | old | new |
|---|---|---|
| `status.FromError.spec` | `Code()` returns `statusCode err`; `Message()` `errDesc err`; `ok = false → errDesc err = m` | `∀ err c m ok`, pre `statusErrOk err ∗ errView err c m ok`; returns `ok`, `Code()` `c`, `Message()` `m` (SpecPlan's shape; all about parameters) |
| `status.Error.spec` | `errDesc err = msg` | post `statusErr err c msg` (uninterpreted; the pin is vacuous: a pointer) |
| **`errors.IsStatusErr.spec`** (P-i; **B1**) | `b = true → errDesc err = errDesc target` (+ T3) | `∀ err target m m'`, pre `statusErrOk err ∗ descIs err m ∗ descIs target m'`; post `⌜b = true → (err = target ∨ m = m') ∧ T3⌝`. Revision 1's `b = true → m = m'` is **false** (review 1, B1: Go's `err == target` shortcut reads no description, and a looping `Error()` gives `descIs e m` for every `m`; `TestIsSelfLoop`/`TestIsSelfFlip` pass in Go) |
| **`fmt.ErrorfWrap.spec`** (P-i; **B2**) | post `errorfWrapIs err inner pre ∗ ⌜pre <+: errDesc err⌝` | post `errorfWrapIs err inner pre` only (the conjunct **deleted**); `∃ s, descIs err (pre ++ s)` is the proved `errorfWrap_descIs` (probe). Revision 1's `errorMsgIs inner m`/`descIs err (pre ++ m)` is **false of the model** (review 1, B2: `Errorf.impl` is `errors.New(format)`, `TrustedCode/fmt.lean:27-28`) |
| `grpc.model.respond.spec` | pre `⌜err ≠ nil ∧ errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)` | `∀ … m`, pre `descIs err m ∗ (⌜err ≠ nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m)` (T8': grpc's server reads `Error()`/`GRPCStatus()` in `status.Convert`, after `m` is fixed) |
| handler outcome clause, `grpcInvokerOk` outcome | `⌜… errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)` | `∃ m, descIs err m ∗ (⌜err ≠ nil ∧ m ∈ handlerDescs⌝ -∗ Ψe m)`; the invoker's error is a `*status.Error` (type stated: pin vacuous, not an `EtcdError`) |
| `waitRetryBackoff.spec` | `errDesc err ∉ handlerDescs` | `∃ m, descIs err m ∗ ⌜m ∉ handlerDescs⌝` |
| `rpctypes.errDesc_etcdError` | axiom (pure) | **deleted**; `descIs_etcdError` (proved, probe) |
| 16 `rpctypes` `Err*_init` | `⌜errDesc e = lit⌝` | the `EtcdError` ones (`ErrFutureRev`, `ErrCompacted`, `ErrUserEmpty`, …): **a pure fact of the value**, `⌜e = mkOk EtcdError.ty #x ∧ x.desc = lit⌝` (I5; `descIs` follows by the law); the `*status.Error` ones (`ErrGRPC*`): `statusErr (ok e) code lit` |
| `errStringToError_init` | `∀ k v, m !! k = some v → errDesc v = k` | `□ ∀ k v, ⌜m !! k = some v⌝ → descIs v k` (values are `*status.Error`s: pin vacuous) |
| `toGRPCErrorMap_init` / `grpcErrMapOk` | pure, over `errDesc` of pointer keys and values | an `IProp`: `[∗ map] k ↦ v ∈ M, ∃ mk mv, descIs k mk ∗ descIs v mv ∗ ⌜mv = futureRevDesc → k = kf⌝ ∗ … ∗ ⌜mk ∉ readDescs⌝`; the cell wand unchanged |
| `grpcErrMethodsOk`, `statusErrOk`, `srvErrOk`, `rpctypesInit` | `grpcStatusRO s (statusCode e)`; `errDesc` | §2.2 forms (names kept) |
| `isHaltErr.spec`, `leasingKV.acquire` (proved) | `statusCode err` | pre `errView err c m ok`, `c` in the post |

**The restated chains (M1; not mechanical).** Each carries one `m` from its producer to the call that
fixes it, and uses the value pin where the code compares by identity:

- **`rpctypes.Error.spec`** (translated, proved): pre `descIs err m` (was `errorMsgIs … m`); post `descIs
  err' m` with the same `m` (Go: `err' = err` when `m ∉ dom errStringToError`, else `EtcdError{code, m}`,
  whose `descIs` is the law), plus `⌜err' = err ∨ ∃ c, err' = mkOk #⟨c, m⟩⌝` (pure).
- **`Client.shouldRefreshToken`** (`Client__shouldRefreshToken.lean:69-79`): pre `descIs err m`; post `b =
  true → m ∈ refusalDescs`. Proof: `rpctypes.Error` gives `descIs err' m`; `IsStatusErr(err', ErrUserEmpty)`
  with `m' := xUE.desc` (law) gives `err' = eUE ∨ m = xUE.desc`; the identity branch gives `m = xUE.desc` by
  the pin; `xUE.desc` is the initializer's literal. Same for `ErrInvalidAuthToken`, `ErrAuthOldRevision`.
- **k8s `store.listReadError`** (`store__listReadError.lean:66`): `readErrIs`/`rangeErrSound`/`rangeErrOut`
  carry `∃ m, descIs err m ∗ □(⌜m = futureRevDesc⌝ -∗ ⌜T3⌝ -∗ …)`: **probed** (`listRead_step`).
- **`isSafeRetry*`**: `IsStatusErr(err, ErrGRPCNotSupportedForLearner)` (a `*status.Error`, a pointer
  target): the identity branch gives `err = that pointer`, whose description the initializer fixes as
  `statusErr`; the consumer's goal is stated as `∃ m, descIs err m ∗ P m`, so it takes the initializer's
  `m` there, not the producer's (no agreement: a fresh existential).
- **The server's Range error path** (`ServerKVOn.rangeErrOther_facts`, `rangeErrDesc_of_grpcErrOut`,
  `ReadOn.rangeErrDesc`, `mvcc.rangeKeysErr`): `rangeErrDesc` becomes `∃ m, descIs err m ∗ (⌜m ≠
  futureRevDesc⌝ ∨ …) ∗ …`; the `rangeKeys` wrap's `m` is `pre ++ s` from `errorfWrap_descIs`.

Every row's (a)/(b)/(c) check: each is a triple, a definition in a triple's pre/post, or a proved law; none
is an entailment with a pure conclusion about a pointer (I2); every pure post fact is about a parameter fixed
in the pre, a returned value, or a pointer-free value (I3, I5); the leaves have no law and no interpreted
producer (I4, I4'). The second reviewer should re-run this check on the final Lean texts (Step 4).

---

## 4. Closed and exported statements touched (completed after review 1, (4))

- **Closed statements (Adequacy/MainLinked): no text change** (review 1 scanned 147 files and confirms).
  The trust base only shrinks or restates: deleted axioms `incomingOf_cancelCtx`,
  `v3rpc.incomingOf_cancellableContext`, `rpctypes.errDesc_etcdError`, `context.WithCancelValCtx.wp_proof`,
  maybe `context.WithTimeoutBackgroundMd.wp_proof`; deleted opaques `incomingOf`, `outgoingOf`, `errDesc`,
  `statusCode`, `grpcStatusROP`, `transportMD`, `builtRawMD`; added opaques `transportMDRaw`,
  `builtRawMDRaw`, `statusAt` (no laws); ~40 trusted texts restated (§3). **Meaning changes through
  redefined vocabulary** (Q9): every closed etcd and k8s theorem's premises that mention `statusErrOk`,
  `libCtxOk`, `ContextReadErrs` keep their text and change meaning with the definitions (none gains a
  conjunct a caller must newly discharge; `libCtxOk` loses one).
- **Exported statements whose text or meaning changes** (for approval, Q9):
  - `client_range_any` (`client/v3/Results.lean:2865`) through `rangeErrOut`: `rangeErrΨ … (errDesc err)` →
    `∃ m, descIs err m ∗ rangeErrΨ … m` (the context-error disjunct unchanged). Its users change in step 2:
    k8s `watchChan__syncPaginated.lean:108`, examples `txnlin/Calls.lean:344`, `ClientPutGet.lean:298`,
    `Results.lean:3168`.
  - `range_end_to_endM` (`v3rpc/Results.lean:514-515`): `rangeErrDesc … err` (an `errDesc` disjunction,
    `ReadOn.lean:294`) → the `∃ m, descIs err m ∗ …` form; `srvErrOk err` (meaning, §2.2). `put`,
    `deleteRange`, `txn_end_to_endM` (`:413, 463, 583`): `srvErrOk err` (meaning).
  - `put/deleteRange/range/txn_end_to_endM`, `authWrapOut_userAdd` (`v3rpc/Results.lean:392, 442, 492, 554,
    862`): `auth.ctxTokenOf ctx` → a quantified `tok` with the premise `auth.ctxTokenIs ctx tok`
    (dischargeable and not vacuous: the callers `etcd_putHandlerM` etc., `client/v3/Results.lean:1210, 1248,
    1391, 1419, 1561, 1897`, receive `ctxInMD ci md` with the handler's metadata; review 1, (4)).
  - `etcdserver/Results.lean:657, 719, 780, 825`: `context.libCtxOk ctx` (meaning: no incoming part, M2).
  - `authkv_bad_unbound` (examples auth `Results.lean:123`): premises `deliversOutgoing c h`, `mdVals
    (outgoingOf c) "token" = [badToken]` → `ctxInMD h (some md) ∗ ⌜mdVals md "token" = [badToken]⌝`, and its
    conclusion `ctxBound (.on γa) h a …` → `ctxBound (.on γa) (mdTokenOf md) a …` (M1's re-indexing; the
    statement says "the auth info bound to the token the context carries").

---

## 5. Go evidence

Behavior the new texts claim (go1.27.3, grpc v1.84.0, the etcd pin):

- `FromIncomingContext(ctx)` reads `ctx.Value(mdIncomingKey{})`, asserts `MD`, copies (grpc
  `metadata/metadata.go:268-282`); `FromOutgoingContext` reads `mdOutgoingKey{}`'s `rawMD`.
- `*cancelCtx`/`*timerCtx` and etcd's `cancellableContext` answer other keys as their parent:
  `examples/axiomcx/incomingof` `TestWrapperInheritsIncoming`, `TestIncomingNotConstant`;
  `examples/axiomcx/incomingof-attack` (`TestRealGrpcTwoStreams` …), re-run 2026-11-18: `ok`.
- `FromError`'s paths: `examples/axiomcx/incomingof-real` `TestFromErrorNoGRPCStatus`, `TestCtxErrDescs`;
  stability: `examples/axiomcx/fromerrorflip`; the wrapped-status code (m4): `status.go:112-125`.
- **`errors.Is`'s identity shortcut (B1)**: go1.27.3 `src/errors/wrap.go:54-57`; review 1's scratch test
  (`…/scratchpad/isloop/isloop_test.go`: `TestIsSelfLoop`, `TestIsSelfFlip` pass). Step 0 moves it into
  `examples/axiomcx/perheap/` (Go test that `errors.Is(e, e)` is `true` for an `Error()` that loops).
- `fmt.Errorf`'s model (B2): `TrustedCode/fmt.lean:20-28`; Go's `*fmt.wrapError`: `fmt/errors.go:46-49`.
- The transport's `MD`: built once in `operateHeaders`, handed to a tap handle after `NewIncomingContext`
  (m3); Step 1 adds a Go test that etcd's server has no tap handle and that a handler's
  `FromIncomingContext` copy is independent of the context's map.

## 5a. H0: a separate early hot fix of F1, on `lean` now

F1 is a Lean-level defect today (review 1, (5)): two closed programs `Errorf("A%w", e)`, `Errorf("B%w", e)`
with the result allocated at one address give `"A" <+: errDesc v ∧ "B" <+: errDesc v`. H0 removes it without
the redesign, in the current `errDesc` vocabulary, so it can land in days.

- **The deletion alone breaks one proof.** The conjunct's only consumer is `mvcc.rangeKeysErr`
  (`InvStore.lean:5632-5637`, conjunct `⌜"rangeKeys: context cancelled: " <+: errDesc err⌝`), used by
  `ServerKVOn.rangeErrOther_facts` (`ServerKVOn.lean:961-982`) for (i) `e ≠ kf ∧ e ≠ kc` (the wrap is
  neither of mvcc's read errors, `togRPCError`'s map lookup) and (ii) `ctxPassed e -∗ rangeErrMsgOk
  (errDesc e)` (the description the server sends for a passed-through wrap). Without it neither holds:
  `errDesc` of the wrap is then unconstrained, and nothing distinguishes it from `kf`. (`ServerKVOn.lean:783`
  uses only the `Error()` WP part.)
- **H0's text (the minimal sound one).** In `Spec/fmt/ErrorfWrap.lean`:
  1. the post's conjunct `⌜pre <+: errDesc err⌝` becomes `⌜methodSet err.ty !! "Unwrap" = some (Signature []
     false [error]) → pre <+: errDesc err⌝`: a fact of Go's `*fmt.wrapError` only (it has `Unwrap`), true
     per run as before, and **vacuous in the model**, whose error is an `*errorString` with no `Unwrap`
     (`ErrorStringLeaf.leaf`, the generated method set): adequacy over the model yields no `errDesc` fact, so
     F1's two runs give nothing;
  2. `fmt.modelErrIs` gains the model's cell, `errStrCell x (pre ++ s)` (`Proof/errors/NewVarCell.lean:38`):
     true of the model (`errors.New` allocates the `errorString` and never writes it; Perennial's
     `wp_New_errorString` persists the field), and in the model's disjunct only, so Go's side is untouched.
- **Consumers to repair** (file:line):
  - `Spec/fmt/ErrorfWrap.lean:35-40` (`modelErrIs`), `:113` (post), `Proof/fmt/ErrorfWrap.lean` (docstring);
  - `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvStore.lean:5632-5637`: `rangeKeysErr` keeps the
    conditional conjunct and the `errorfWrapIs` disjunction (in place of the bare prefix);
  - `…/mvcc/storeTxnCommon__rangeKeys.lean:687-708`: builds it (pattern `%Hpre` → the implication);
  - `…/v3rpc/ServerKVOn.lean:961-982`: case on the disjunct — Go's: the prefix from the implication, as
    today, and (i) by method set (`*wrapError` has `Unwrap`; `kf`, `kc` are `*errorString`s, leaves); the
    model's: (i) by the cells (`errStrCell x (pre ++ s)` against `kf`'s and `kc`'s `errVarCell`, in
    `mvccInit`, `mvcc/Base.lean:264-265`; the prefixes differ), (ii) by `ctxPassed` (an `*errorString` is a
    leaf without `Is`, so `ctxPassed e` makes it `Canceled`'s or `DeadlineExceeded`'s value, whose
    description `ctxErrDescs` gives: the existing `Hcx` step);
  - `…/v3rpc/ServerKVOn.lean:783`, `Proof/go_etcd_io/etcd/cache/v3/Base.lean:901-933` (`ctxWrapErr_wrap*`),
    `…/txn/executeTxn.lean:384`: `icases` patterns of `modelErrIs` (one more conjunct).
- **Cost:** 7 files, ~100 lines, 1.5–2 days (the `modelErrIs` change rebuilds everything importing
  `cache/v3/Base`: one full build). No exported or closed statement changes; one trusted text restated
  (`fmt.ErrorfWrap.wp_proof`): hard stop for approval, and an `axiom`-skill review with the cross-world
  check (the new conjunct is an implication with a pure conclusion about `errDesc` of an allocated value,
  sound because its antecedent is false of every value the model allocates; the cell is a model fact).
- `errors.IsStatusErr` needs no hot fix (§1.2, F1 paragraph). The redesign's step 2 then deletes the
  conditional conjunct with `errDesc` (B2's deletion), keeping the cell.

---

## 6. Steps, estimates, checkpoints (re-estimated after review 1, (6))

Each phase lands on its own (`etc/land.sh` after the coordinator's go), in place (no twin specs).

| step | what | files (text edits) | lines (est.) | time (agent-days) |
|---|---|---|---|---|
| H0 | §5a, on `lean`, independent of the rest | 7 | 100 | 1.5–2 |
| 0 | Vocabulary (§2, SpecPlan names; leaves with `hG`); laws incl. `descIs_etcdError` (+ `IntoValInj EtcdError`), `errorfWrap_descIs`, the transfer laws; the probes' theorems in the tree; **errors probe against the real consumers** (`listReadError`, `shouldRefreshToken` with the restated `IsStatusErr`/`rpctypes.Error`, on a scratch branch: `lean-check` only); the Go test for B1; ledger entries 1–2 decided | 6 | 500 | 3–4 |
| 1 | **Incoming** (§3.1): delete `incomingOf`, the two axioms; FromIncomingContext/WithValue/Tracer.Start/EnsureTrace; grpc contracts with the single source (M2: `grpcAccepted`, `libCtxOk`, `srvRawStreamIs`, `srvStreamInterceptorWOk`, `newStreamInterceptor`); 16+3 handler specs; **C1a** (the `ctxBound` family by token, `AuthInfoFromCtx`/`AuthInfoFromTLS`, 38 files); server `Hinc` lemmas; v3rpc Results (5) | ~110 | 2000 | 10–13 |
| — | **C1a** (first), **C1**: builds; `tcb-report --check --update` shows the two axioms gone from 22 collections; interfaces regenerated; stop, land | | | |
| 2 | **Errors** (§3.3): delete `errDesc`, `statusCode`, `grpcStatusROP`, `errDesc_etcdError`; FromError/Error/IsStatusErr/ErrorfWrap/respond/waitRetryBackoff; inits (17), `toGRPCErrorMap_init`; `statusErrOk` family (198 files rebuild); handler outcomes; the restated chains (server Range path, `rpctypes.Error`, `shouldRefreshToken`, `isSafeRetry*`, `rangeErrOut`/`rangeErrSound`/`readErrIs`, `listReadError`, leasing `acquire`, `isHaltErr`); `client_range_any`'s users (syncPaginated, txnlin) | ~80 | 2600 | 12–16 |
| — | **C2a** (first): the server's Range path **and** `listReadError`, `shouldRefreshToken` converted and `lean-check`ed; report. **C2**: builds; stop, land | | | |
| 3 | **Outgoing** (§3.2): delete `outgoingOf`, `builtRawMD`; `outgoingCtxOkC` redefined (110 files rebuild, ~31 edited); Append/withVersion/streamKeyFromCtx; `WithCancelValCtx`/`WithTimeoutBackgroundMd` as corollaries; `grpcAttemptMd`/`grpcInvokerOk`/`clientAttemptMdOf`/`credsYield`; client watch; examples auth, `authkv_bad_unbound` | ~45 | 1400 | 6–8 |
| — | **C3**: builds; stop, land | | | |
| 4 | The rest of §1.3 (Q7); `notes/axiom-review/perheap.md` (final texts, (a)/(b)/(c)/I4' per text), audit rows, `incomingof-crossworld.md` closed, the `axiom` skill's cross-world paragraph with (I1)–(I5) | ~10 | 300 | 2–3 |
| all | Per phase: merges of `lean`, two full builds (~12.8k modules, 45G slot, retries), 68 collection baselines, interface regeneration, handoffs | | | 4–6 |

Total: ~250 files edited (362 touched), ~6900 lines, **39–52 agent-days, 8–10.5 weeks** (review 1: 7–9;
revision 1: 5–6.5). The largest uncertainty is step 2's chains: C2a measures them before the rest.

---

## 7. Risks

- **R1. Proofs that use `errDesc` as a function** (the chains of §3.3). Each must carry one `m` from the
  producer to the consumer's call, with the value pin where the code compares by identity; probed for
  `listReadError` only. C2a measures the rest first.
- **R2. A proof needs agreement after all** (two relations of one value, no call between, not an
  `EtcdError` value). Stop: an agreement law needs its own review (§2.3a).
- **R3. Build cost and memory** (rebuild of most of the tree per phase; `[∗list]`/`List.replicate` contexts
  framed explicitly).
- **R4. Meaning of "∃ m, descIs err m ∗ P m"** (partial correctness: for a looping `Error()` any `m`
  works, but nothing that reads the description returns). Stated in the docstrings of `rangeErrOut`, the
  handler contracts and `descIs`.
- **R5. The secondary family** (§1.3): Q7.
- **R6. Interference with other sessions** (shared grpc contracts, `cache/v3/Base`): land each phase soon
  after its checkpoint.
- **R7. SpecPlan divergence** (ledger 1–2): if the user keeps `ctxInMD_agree`, step 1 needs the opaque
  realization of §2.3a instead (two trusted transfer entailments, a model argument), and the proved
  transfer laws go: +3–5 days and a separate review.
- **R8. `go.IntoValInj EtcdError`**: the value pin's law needs it; if `go.BasicIntoValInj` is not available
  to the closed theorems, Step 0 states the pin through a field projection of the `val` instead.

---

## 8. Open questions (each with a recommendation)

- **Q1. Order.** Recommend: **H0 now** (independent, on `lean`); then step 0 (with the errors probe against
  real consumers and the B1/B2 texts); step 1 incoming (C1a first); step 2 errors (C2a first, incl.
  `listReadError`/`shouldRefreshToken`); step 3 outgoing; step 4 rest. Each landed separately.
- **Q2. Agreement laws.** Recommend **none**; ledger entry 1 proposes deleting SpecPlan's `ctxInMD_agree.spec`
  (false for the defined realization; sound only as an opaque with trusted transfers and a model, which
  nothing needs; §2.3a). User decision (a SpecPlan law).
- **Q3. `ctxInMD` defined or opaque.** Recommend **defined** over Perennial's `ctxValue` (both refuted axioms
  become theorems), opaque only at the `MD` leaf, no `_raw` law.
- **Q4. Error relations.** Recommend SpecPlan's `errView`/`statusErr`/`errMsg`/`plainErr`/`statusAt` for
  `FromError`, plus **`descIs`** (message, with the value pin) for the description reasoning; ledger entry 2
  (`errView`'s missing wrapped-status case). Revision 1's single `errStatusIs` is withdrawn (its
  no-`GRPCStatus` branch claimed `Unknown` for wrap errors, m4).
- **Q5. `rpctypes.errDesc_etcdError`.** Recommend **delete** (proved `descIs_etcdError`, probe).
- **Q6. `WithTimeoutBackgroundMd`, `WithCancelValCtx`.** Recommend both as corollaries of Perennial's proved
  `WithTimeout`/`WithCancel` (m6), deleting the axioms; restate only what Perennial's specs do not give.
- **Q7. The secondary family.** Unchanged: step 4 replaces `transportPeer`, `otelSpan`, `builtTrace` (beside
  `transportMD` in `libCtxOk`) by raw `IProp` leaves; the per-run-only ones are recorded in
  `notes/axiom-review/perheap.md`; the `axiom … : Prop` pointer predicates classified there.
- **Q8. F1.** Recommend (changed): **the H0 hot fix now** (§5a: conditional conjunct + the model's cell; 7
  files, 1.5–2 days, one trusted text restated: approval + axiom review), with the audit row; the redesign
  deletes the conjunct in step 2. Revision 1's "no hot fix" is withdrawn: F1 is a Lean-level defect today.
- **Q9. Exported statements** (§4, completed): approve the listed text changes (`client_range_any`,
  `range_end_to_endM`'s `rangeErrDesc`, the five `tok` premises, `authkv_bad_unbound` with `ctxBound` by
  token) and the meaning changes through `srvErrOk`/`statusErrOk`/`libCtxOk`.
- **Q10. `membership.memBucketsOk`.** Unchanged: a separate `axiom`-skill review of
  `clusterImageOk_restModel.wp_proof`, before step 4.
- **Q11 (new, B1). `errors.IsStatusErr`'s post.** Recommend `b = true → (err = target ∨ m = m') ∧ T3`, the
  identity as an equation of interface values (consumers rewrite with it; for `EtcdError` targets the pin
  turns it into `m = m'`).
- **Q12 (new, M1). The value pin in `descIs`.** Recommend yes (I5: a pure fact of a pointer-free value, true
  in Go, proved by every producer; it is what lets the identity branch close the `EtcdError` chains without
  agreement: probe `listRead_step`).
- **Q13 (new, M1). The `ctxBound` family by token.** Recommend `ctxBound M (tok : Option GoString) a` (and
  `principalBound`, `noPrincipalFrom`, `tokRefusedFrom`, `userAttemptOk` likewise), `AuthInfoFromCtx` with
  `md` a parameter; checkpoint C1a.
- **Q14 (new, M2). One source of a run context's `ctxInMD`.** Recommend: remove the incoming part from
  `libCtxOk`/`grpcRunCtx`/`srvRawStreamIs`; `grpcAccepted` is the only producer; the stream interceptor
  contract passes the stream's `ctxInMD ci md` in.
- **Q15 (new, m1). Leaves with `hG`, and (I4').** Recommend yes; Step 4 checks (I4') per text.
- **Q16 (new). SpecPlan names.** Recommend adopting them (§2.0) in `Spec/`/`Proof/`, with ledger entries
  for the two divergences.

---

## 9. Review 1, item by item

| item | answer |
|---|---|
| B1 (`IsStatusErr` post false) | §3.3 row, Q11; probed (`IsStatusErrP.spec`, `listRead_step`) |
| B2 (`ErrorfWrap` post false of the model) | §3.3 row (conjunct deleted, `errorfWrap_descIs` proved in the probe); H0 (§5a), Q8 |
| M1 (agreement chains) | value pin (§2.2, Q12); restated chains (§3.3: `rpctypes.Error`, `shouldRefreshToken`, `listReadError` probed, `isSafeRetry*`, Range path); `ctxBound` family by token, `AuthInfoFromCtx` with `md` (§3.1, Q13); C1a |
| M2 (two sources of incoming metadata) | §3.1 (`libCtxOk`/`grpcRunCtx`/`srvRawStreamIs` lose the incoming part; `srvStreamInterceptorWOk` passes it), Q14 |
| SpecPlan (MAJOR, process) | §2.0 names adopted; §2.3a `ctxInMD_agree` (ledger entry 1); `errView` gap (ledger entry 2); Q2, Q4, Q16 |
| §4 omissions | §4 completed (`range_end_to_endM`'s `rangeErrDesc`, `srvErrOk` in four, `etcdserver/Results` `libCtxOk`, `client_range_any`'s users, `authkv_bad_unbound`'s real shape) |
| m1 (leaves `hG`-free) | (I4'), §2.1/§2.2 binders, Q15 |
| m2 (transfer laws assumed) | (I2) restated |
| m3 (tap handle) | `transportMDRaw` docstring (§2.1), Step 1 Go test (§5) |
| m4 (`Unknown` for wrap errors) | `errView` needs `plainErr`; `descIs` separate (§2.2), Q4 |
| m5 (`GRPCStatus()` returning nil) | §2.2, stated as incompleteness |
| m6 (`WithCancelValCtx` derivable) | §3.2 row, Q6 |
| Inventory (derived predicates, `incomingCtxOk` specs, outgoing 114/115 files, `status.Code`) | §1.2a |
| Estimate (7–9 weeks) | §6: 8–10.5 weeks |
| Order (errors probe in step 0; C2a with k8s/client; C1a) | §6, Q1 |
| F1 priority | H0, Q8 |
