# Scope: the per-heap redesign — pointer-keyed pure functions become per-run Iris relations

**Status: SCOPE, revision 3 (after independent review 2, `/shared/tmp/perheap/review-2.md`), for a short
independent check, then implementation (hard stop). No Lean changed in the tree.** Branch `perheap-scope`
off `lean` `49bd7924e6` (worktree `/shared/etcd-grove-incomingof`), the perheap agent of etcd-grove-03.
Revision 1: `dda8f5f7d8`; revision 2: `3b10ff2b93` (its full inventory and old→new tables for the errors and
outgoing parts stand as the outline of Part II). Background: `notes/axiom-review/ctx-descs.md`,
`notes/axiom-review/incomingof.md` (Part A refuted), `notes/axiom-review/incomingof-b.md`,
`notes/incomingof-crossworld.md`, `notes/fromerror-wand.md`, `notes/incomingof-scope.md`.

**The user's decisions, 2026-11-18 (via etcd-grove-03):**

1. **H0 is no longer part of this redesign.** A separate branch (fmt-soundness) lands it now:
   `fmt.ErrorfWrap` restated and **proved** (review 2's H0′: `wp_New_errorString_cell`, 20 lines; the axiom
   leaves the trust base) plus a term-level `Errorf` gate. Revision 2's §5a (H0) is withdrawn from this
   Scope; F1 is that branch's (§9).
2. **Incoming first, then decide.** This redesign proceeds with **step 0 and the incoming part only**:
   the two refuted axioms `incomingOf_cancelCtx` and `v3rpc.incomingOf_cancellableContext` become theorems,
   `metadata.incomingOf` goes. The errors and outgoing parts come back to the user afterwards (Part II
   records their state and review 2's findings, no detail).

**The goal (the user's):** no trusted text concludes a pure fact about a pointer-typed value. Opaque Lean
functions of a heap-dependent value become per-run Iris relations; every pure fact a trusted text gives is
about a value fixed in a precondition or returned by the call.

---

## 0. The rule (all parts)

Three ways turn a trusted fact about the Go meaning of a pointer-typed value into a Lean fact about every
heap: **(a) crossWorld** (an entailment from bare persistent points-tos holds in a fresh heap of any
content, `ctx-descs.md`); **(b) the persistent-authoritative fresh world** (`Auth DFrac.discard σ` decides
every points-to and satisfies every WP of a non-value, `incomingof.md`); **(c) adequacy with allocation**
(a pure post fact of code with Lean semantics about an address it allocated, `incomingof-scope.md` §0.2).
The invariant every new text is checked against:

> **(I1)** No trusted text has an opaque *pure* function of a pointer-typed value; what replaces one is a
> persistent `IProp` relation `R x a`.
> **(I2)** No entailment (axiom, premise-class field, law) concludes a pure fact from such a relation: its
> conclusions are relations (transfer laws), each **proved** where the relation is defined or stated in the
> post of a call to uninterpreted code. *Exemption (review 2, m2):* an (I5) fact about a pointer-free value
> that a relation carries inside its definition (the errors part's value pin) may be extracted.
> **(I3)** A pure fact about `a` comes only from a triple whose precondition holds `R x a` with `a` fixed
> before the call, and is about `a` and the call's results.
> **(I4)** The only opaque leaves are `IProp`s made by trusted producers (posts of uninterpreted calls),
> with **no law**. **(I4')** No post of code with Lean semantics produces a leaf, and every leaf takes the
> heap's names (`[hG : HeapGS _ GF]`) in its binders.
> **(I5)** A pure fact a producer gives about a *pointer-free* value (a metadata map value `GrpcMd`, a
> token string, an `EtcdError` struct) is allowed.
> **(P-i test, review 2, m5)** Every trusted text over interpreted code (translated, or a Perennial model
> with an `impl`) must be provable from the Lean semantics with every opaque leaf and relation left
> abstract. (Sharper than "facts only about parameters"; Step 1's per-text check applies it.)

---

# Part I — step 0 and the incoming part (in detail)

## 1. Inventory of the incoming part (at `lean` `49bd7924e6`)

**Counts.** 122 files (`Proof/` + `Spec/`) mention the incoming vocabulary below, 683 occurrences
(`/shared/tmp/perheap/incoming-files.txt`); of them 66 files / 450 occurrences are the auth chain
(`ctxTokenOf`, `ctxBound`, `ctxBoundOrTLS`, `principalBound(I)`, `noPrincipalFrom`, `tokRefusedFrom`,
`hdrBoundM`, `infoBoundM`, `rangeWhy_ctx`/`txnWhy_ctx`, `AuthInfoFromCtx.spec(Lb)`); 21 files state a
handler's `Spec (metadata.incomingOf ci)`. None in `GooseLang/`, `TrustedCode/`, `RaftWitness/`, `RaftTla/`,
`PorcupineDag/`, `WalTester/`; `SpecPlan/` mentions it in 2 files (prose).

| trusted text | file:line | kind | today | in this part |
|---|---|---|---|---|
| `metadata.incomingOf : GoInterface → GrpcMd` (opaque) | `Proof/google_golang_org/grpc/metadata/Incoming.lean:27` | opaque | pure function of a pointer | **deleted** |
| `incomingOf_cancelCtx` (+ `_parent_unique`) | `…/metadata/Incoming.lean:61` | E | `ctxField c ↦□ p ⊢ ⌜incomingOf (*cancelCtx c) = incomingOf p⌝` | **refuted** (a); deleted, `ctxInMD_cancel` **proved** |
| `v3rpc.incomingOf_cancellableContext` (+ `_field_unique`, `incomingOf_wrapper`) | `…/v3rpc/WrapperMd.lean:76` | E | same for etcd's wrapper | **refuted** in meaning; deleted, `v3rpc.ctxInMD_cc` **proved** |
| `metadata.transportMD : GoInterface → Prop` (opaque) | `Proof/context/LibKeys.lean:57` | opaque | "the transport made this `MD`" | replaced by the leaf `transportMDRaw` (§2) |
| `metadata.incomingRes`, `metadata.incomingCtxOk` (defs in `libCtxOk`, `libCtxOkC`) | `LibKeys.lean:137, 159`; `LibKeysChain.lean:67` | D | `∃ v, ⌜incomingRes v⌝ ∗ valueAt ctx mdIncomingKey (· = v)` | `incomingCtxOk ctx := ∃ md, ctxInMD ctx md` (§2, §3) |
| `metadata.FromIncomingContext.wp_proof` | `Proof/…/metadata/FromIncomingContext.lean:23` (spec `Spec/…:37`) | P-u | `ok ↔ incomingOf ctx ≠ none`, result `incomingOf ctx` | restated over `ctxInMD ctx md` (facts about `md`) |
| `context.WithValue.wp_proof` | `Proof/context/WithValue.lean:24` | P-u | `⌜incomingOf c' = incomingOf parent⌝` | `□ ∀ md, ctxInMD parent md -∗ ctxInMD c' md` |
| `traceutil.Tracer.Start.wp_proof` | `Proof/…/traceutil/Tracer__Start.lean:26` | P-u | `⌜incomingOf ctx' = incomingOf ctx⌝` | the same transfer |
| `auth.authStore.AuthInfoFromTLS.wp_proof` | `Spec/…/auth/authStore__AuthInfoFromTLS.lean` | P-u | pre `peerCtxOk ctx ∗ incomingCtxOk ctx` | **text unchanged**; meaning through `incomingCtxOk` |
| `auth.NewAuthStore.wp_proof` | `Proof/…/auth/NewAuthStore.lean:26` (spec `:158`) | P-u | post `isReqAuth st RD` (`InvRequest.lean:2801`: `AuthInfoFromCtx`/`AuthInfoFromTLS` triples under `libCtxOk ctx`) | **text unchanged**; meaning through `libCtxOk` (§3: why it must keep an incoming part) |
| grpc model `acceptRun`/`acceptRunConns` posts: `grpcAccepted` | `Proof/google_golang_org/grpc/InvGrpcRun.lean:134` | D | `▷ Spec (incomingOf ci) m Φ Ψe`; stream `□ Spec (incomingOf ci) γs Dn` | `∃ md, ctxInMD ci md ∗ ▷ Spec md …` (the source of every handler's `md`) |
| `grpcRunCtx` (in `grpcAccepted`; holds `libCtxOk ci`), `srvRawStreamIs` | `InvGrpc.lean:229`; `InvGrpcStream.lean` | D | incoming part through `libCtxOk` | text unchanged (meaning through `libCtxOk`) |
| grpc contracts `grpcHandlerOkMd`, `grpcHandlerOwnOkMd`, `grpcMethodOkMd`, `grpcRunOkMd`, `srvInterceptorOk`, `grpcStream{Handler,Method,Run}Ok`, `srvStreamInterceptorWOk`, `GrpcSpec`, `etcdPkgPrefix` | `InvGrpc.lean:296, 364, 595, 980, 657`; `InvGrpcStream.lean:869, 1235, 1284, 1073` | D (in `grpc.start`'s and the model's statements) | `Spec (incomingOf ci)`; stream `⌜incomingOf ci' = incomingOf ci⌝` | `∀ md, ctxInMD ci md -∗ Spec md …`; the stream interceptor receives and passes `ctxInMD ci md` |

Derived pure vocabulary over `incomingOf` (each moves): `auth.ctxTokenOf` (`server/v3/auth/InvAuth.lean:748`),
`auth.ctxBound` (`:767`), `noPrincipalFrom`, `tokRefusedFrom` (`auth/WhyDefs.lean:48, 59`),
`principalBound`/`principalBoundI` (`etcdserver/AuthBound.lean:58, 182`), `hdrBoundM` (`ReqOn.lean:460`),
`infoBoundM`, `ctxBoundOrTLS` (`AuthReqDerive.lean:92`), `isReqAuthBound` (`InvRequest.lean:2842`),
`srvKVAnsOn`/`srvKVAnsM` (`v3rpc/ServerKVOn.lean`, `⌜on = true → ctxTokenOf ctx = tok⌝`), `lessorGrantOkGM`,
`lessorRevokeOkM` (`v3rpc/LeaseOn.lean`), `ctrlP`, `swsIs` (`v3rpc/InvWatch.lean`), `v3rpc.ctrlMid`
(`serverWatchStream__sendLoop.lean`), `userAttemptOk`, `deliversOutgoing` (examples auth
`ClientAuth.lean:92, 98`), `rangeWhy_ctx`/`txnWhy_ctx` (`ReadWhy.lean:189, 200`, hypothesis `incomingOf c =
incomingOf c'`), `metadata.FromIncomingContext.weakSpec` (`FromIncomingWeak.lean`; no user).
**Token-indexed versions already exist** beside several of these: `principalBoundT`
(`v3rpc/InvLeaseKeepAlive.lean:63`), `hdrBoundT`, `v3rpc.infoBoundT` (`AuthReqDerive.lean:70`). Re-indexing
the context-indexed ones by the token makes them these: they merge (no new family; one fewer).

**Twins found (review 2, MAJOR 2):** `auth.authStore.AuthInfoFromCtx.spec` (proof
`Proof/…/auth/authStore__AuthInfoFromCtx.lean`) and `.specLb` (`FreshCtx.lean:50`, proof `wp_lb` `:73`) are two
specs with two proofs of one Go function; likewise `EtcdServer.AuthInfoFromCtx.spec`/`.specLb`
(`Spec/…/etcdserver/EtcdServer__AuthInfoFromCtx.lean:46, 65`; proofs `wp_proof`/`wp_proofLb` in
`Proof/…/EtcdServer__AuthInfoFromCtx.lean:29, 91`). Both merge in this part (§4.2).

## 2. The vocabulary (step 0)

In `Proof/context/LibKeys.lean` / `LibKeysChain.lean` (SpecPlan's names, §2.0 of revision 2):

```lean
/-- (opaque; TRUSTED; no law) grpc's server transport made the `MD` `v` (a map) holding `f`, with
lower-case keys each with at least one value, and nothing writes it after (`operateHeaders`; etcd's server
installs no `InTapHandle`: Step 1's Go test). -/
opaque metadata.transportMDRaw {GF} [hG : HeapGS HasLC.hasLC GF] (v : GoInterface)
  (f : GoString → Option (List GoString)) : IProp GF
def metadata.incomingHeld (v : GoInterface) (md : GrpcMd) : IProp GF :=
  (⌜md = none ∧ v is not an MD⌝) ∨ ∃ f, ⌜md = some f ∧ ∀ k vs, f k = some vs → vs ≠ []⌝ ∗ □ transportMDRaw v f
/-- **`ctx`'s incoming metadata is `md`** (persistent, per heap), over Perennial's chain. -/
def metadata.ctxInMD (ctx : GoInterfaceOk) (md : GrpcMd) : IProp GF :=
  ∃ v, context.ctxValue ctx mdIncomingKeyAny (· = v) ∗ incomingHeld v md
/-- **`ctx`'s incoming metadata is grpc's** (kept name, redefined): what `libCtxOk` carries. -/
def metadata.incomingCtxOk (ctx : GoInterfaceOk) : IProp GF := ∃ md, ctxInMD ctx md
/-- **The token `ctx` carries is `o`** (SpecPlan's `Auth.ctxToken`, `SpecPlan/…/auth/Api.lean:505`). -/
def auth.ctxToken (ctx : GoInterface) (o : Option GoString) : IProp GF :=
  ∃ c md, ⌜ctx = ok c⌝ ∗ metadata.ctxInMD c md ∗ ⌜auth.mdTokenOf md = o⌝
/-- **`a` is bound to the token `tok`** (`ctxBound`, re-indexed by the token). -/
def auth.ctxBound (M : AuthMode) (tok : Option GoString) (a : Loc) : IProp GF :=
  ⌜a = null⌝ ∨ ∃ t, ⌜tok = some t⌝ ∗ infoBound M t a
```

- **Laws (all proved; none trusted):** `ctxInMD_cancel`, `_timer`, `_valueCtx` (another key), `_from`
  (`ctxValueFrom`), `_background`/`_todo` (`none`), `v3rpc.ctxInMD_cc` (etcd's wrapper), `ctxInMD_valueAt`
  (the `valueAt` form readers use), persistence. The two refuted axioms' replacements are proved in the probe
  (§6). `libCtxOk`'s producers (`libCtxOk_of_ctxValueNil`, `_background`, `_todo`, `_bgFrom`,
  `_of_valueWand`, `_of_nil`) give `incomingCtxOk` through these; `_of_nil` (6 users) from a `valueAt` at a
  foreign context type, through `ctxChain`'s foreign root (`Perennial/Proof/context/CtxValue.lean:79-82`).
- **`HasLC.hasLC` (form).** `ctxValue` is stated at `HasLC.hasLC`; `ctxInMD`, hence `incomingCtxOk` and
  `libCtxOk`, move from `{hlc}` to `HasLC.hasLC`, with the ~12 `{hlc}`-generic files that take them
  (`FromIncomingContext`, the auth store's `AuthInfoFromCtx`/`AuthInfoFromTLS` and its proof files, the grpc
  sections at `InvGrpc.lean:795`, `InvGrpcStream.lean`). Every caller is at `HasLC.hasLC` already. Q3.
- **What is deleted:** `incomingOf`, the two axioms and their `_unique`/`_wrapper` lemmas, `transportMD`,
  `incomingRes`, `auth.ctxTokenOf`, `rangeWhy_ctx`/`txnWhy_ctx`, `FromIncomingContext.weakSpec` (no user; or a
  two-line corollary).

## 3. Review 2's MAJOR 2: what the auth-off theorems need, and why `libCtxOk` keeps an incoming part

Revision 2 removed the incoming part from `libCtxOk` (review 1's M2, "one source"). Review 2 found that this
breaks the auth-off exported theorems (`etcdserver/Results.lean:652, 714, 774, 819`, which take only
`libCtxOk ctx` for an arbitrary `ctx`) unless `AuthInfoFromCtx` needs metadata only when auth is on. Revision
3 adopts that gate **and** finds that it is not enough on its own:

- **The store's `AuthInfoFromCtx` reads metadata only when auth is on** (true of Go: `store.go`
  `AuthInfoFromCtx` returns `nil, nil` on `!as.IsAuthEnabled()` before `FromIncomingContext`). In the model,
  `.off`'s verdict is `false` (`enabledVerdictFrom .off _ b = ⌜b = false⌝`, `auth/Fresh.lean:58`), so the
  read branch is absurd there: **probed** (§6, `spec_off`).
- **But the server's `AuthInfoFromCtx` reads the incoming metadata whatever the auth mode** when the TLS
  fallback is on: `v3_server.go:1206-1216` calls `AuthInfoFromTLS(ctx)` after the store's `(nil, nil)` when
  `ClientCertAuthEnabled`, and `AuthInfoFromTLS` (`store.go:1025-1069`) calls `metadata.FromIncomingContext`
  (`:1044`) for a TLS peer with a verified chain (the gateway check). `cca` is the server's configuration
  (`srvCfgFieldAddr s "ClientCertAuthEnabled" ↦□ v.cca`, arbitrary in the auth-off theorems).
- **And the real store's request side is stated for every mode under `libCtxOk` alone**:
  `isReqAuth_of_authInv` (`AuthReqDerive.lean:113`) proves `isReqAuth` (`InvRequest.lean:2801`: both
  triples under `libCtxOk ctx ∗ ctxDoneAny ctx`) for any `M`, and `isReqAuth` is the post of the trusted
  `auth.NewAuthStore.wp_proof`. With auth on, the store's read needs an `md` for the context; it can come only
  from `libCtxOk`.
- **Finding (about revision 2's plan, not the tree):** with `libCtxOk`'s incoming part removed, the trusted
  `NewAuthStore` post would promise `AuthInfoFromTLS` is safe for a context whose `Value(mdIncomingKey{})`
  panics (with a TLS peer), which is false in Go. Revision 3 withdraws that removal.

**Decision of revision 3 (Q14, replaces revision 2's).** `libCtxOk` keeps an incoming part, redefined as the
anonymous `metadata.incomingCtxOk ctx = ∃ md, ctxInMD ctx md` (its text, and that of `AuthInfoFromTLS`,
`NewAuthStore`, `grpcRunCtx`, `isReqAuth` and the four auth-off theorems, unchanged). **The `md` a spec is
about comes from one source, `grpcAccepted`** (with `Spec md`); every spec that relates a context's metadata to
something else takes `md` (or the token) as a parameter, never from `libCtxOk`'s existential. Two existentials
for one context are harmless: no law relates them (no agreement, §5), so no proof can derive anything from
having both; and both are true in Go (the same map). Review 1's M2 case (`newStreamInterceptor`) is closed by
the contract: `srvStreamInterceptorWOk` passes the stream's `ctxInMD ci md` in, and the interceptor reads with
it (§4.1).

## 4. Old → new (incoming)

### 4.1 Texts

| text | old | new |
|---|---|---|
| `incomingOf_cancelCtx`, `v3rpc.incomingOf_cancellableContext` (+ lemmas) | axioms | **deleted**; `ctxInMD_cancel`, `v3rpc.ctxInMD_cc` proved |
| `metadata.FromIncomingContext.spec` (P-u) | pre `incomingCtxOk ctx`; post on `incomingOf ctx` | `∀ ctx md`, pre `ctxInMD ctx md`; post `⌜ok = false ∧ md = none⌝ ∨ ∃ md0 m, ⌜ok ∧ md = some md0 ∧ dom m = dom md0⌝ ∗ mp ↦$ m ∗ [∗map] …` (facts about `md`; probe `FromIncomingContextQ.spec`) |
| `context.WithValue.spec` (P-u) | `⌜incomingOf c' = incomingOf parent⌝` | `□ ∀ md, ctxInMD parent md -∗ ctxInMD c' md` |
| `traceutil.Tracer.Start.spec` (P-u), `EnsureTrace.spec` (proved) | `⌜incomingOf ctx' = incomingOf ctx⌝` | `□ ∀ md, ctxInMD ctx md -∗ ctxInMD ctx' md` |
| `grpcAccepted` (model post; **the source**) | `▷ Spec (incomingOf ci) m Φ Ψe`; stream `□ Spec (incomingOf ci) γs Dn` | one more existential `md`: `ctxInMD ci md ∗ ▷ Spec md m Φ Ψe`; stream `ctxInMD ci md ∗ □ Spec md γs Dn` |
| handler/method/run contracts (`grpcHandlerOkMd`, `grpcHandlerOwnOkMd`, `grpcMethodOkMd`, `grpcRunOkMd`, `srvInterceptorOk`, `grpcStream{Handler,Method,Run}Ok`) | pre `Spec (incomingOf ci) …` | `∀ … md`, pre `ctxInMD ci md ∗ Spec md …` |
| `srvStreamInterceptorWOk` (`newStreamInterceptor.lean:220, 264-268`) | handler gets `⌜incomingOf ci' = incomingOf ci⌝`; interceptor reads `incomingCtxOk` from `libCtxOk_of_runCtx` | the interceptor receives `ctxInMD ci md`, reads with it (`FromIncomingContext` at `md`), and passes `ctxInMD ci' md` to the handler |
| 16 handler specs (`_KV_*`, `_Lease_*`, `_Auth_*`, `_Watch_Watch` `_Handler`), 3 `quota*`, 4 `LeaseServer.*`, `watchServer.Watch` (proved) | as the contracts | as the contracts |
| `libCtxOk`, `grpcRunCtx`, `srvRawStreamIs`, `isReqAuth`, `AuthInfoFromTLS.spec`, `NewAuthStore.spec` | incoming part `incomingCtxOk` | **text unchanged**; `incomingCtxOk` redefined (§2) |

### 4.2 The auth chain, by token (checkpoint C1a; review 2 MAJOR 2, the twins)

- **`auth.authStore.AuthInfoFromCtx.spec` — one spec** (today's `specLb`, the stronger), by token, the
  metadata gated by the mode (PRINCIPLES, "One spec, a gated row"):
  `∀ st R M n ctx (tok : Option GoString)`, pre `… ∗ □ (⌜M.isOn = true⌝ → auth.ctxToken ctx tok) ∗ tpReady M ∗
  ctxDoneRecv ctx ∗ authPubLbM M n`; post `… ∗ ctxBound M tok a ∗ (a = null ∧ err = nil → noPrincipalFrom M n
  tok) ∗ (err ≠ nil → … ∗ tokRefusedFrom tok) ∗ (a ≠ null → enabledVerdictFrom M n true)`. **Proved in the
  probe** (§6), the whole proof (both the `token` and `authorization` branches).
  Today's `.spec` (no lower bound) becomes **the corollary** `AuthInfoFromCtx.spec_w : spec → specW` (floor
  `0`, `authPubLbM_zero`: proved in the probe); `wp_proof` of the old `.spec` (~250 lines) is deleted. Callers
  that took `.spec` (`AuthApplyOn.lean:63`, `AuthBound.lean:216`, `AuthSrv.lean:428, 668`,
  `AuthReqDerive.lean:114, 152`, `Link.lean:1344`) take `specW` (a corollary) or the spec.
- **`EtcdServer.AuthInfoFromCtx.spec` — one spec** (today's `specLb`), by token: pre adds
  `□ (⌜M.isOn = true⌝ → auth.ctxToken ctx tok)` (the store's read) and keeps `context.libCtxOk ctx` (the TLS
  fallback's read, §3); post `□ (⌜M.isOn⌝ → ctxBoundOrTLS s M tok a)` and the `specLb` rows at `tok`. Today's
  `.spec` a corollary (`spec_w`); `wp_proof` (one of the two proofs) deleted. Callers: `checkLeaseTimeToLive`,
  `checkLeaseRenew`, `processInternalRaftRequestOnce`, `ReqOn.lean:830` (`.spec`); `requireAuthInfo`,
  `checkMembershipOperationPermission`, `doSerialize`, `AuthAdmin.isPermitted`, `isWatchPermitted`,
  `ReqOn.lean:867` (`.specLb`).
- **`isReqAuthBound`** (`InvRequest.lean:2842`, a definition, not trusted): its `AuthInfoFromCtx` triples take
  `tok` and `□ (⌜M.isOn⌝ → ctxToken ctx tok)`, post `ctxBound M tok a`. **`isReqAuth`**: unchanged (the
  unbound side; its real-store proof takes `tok := mdTokenOf md` from `libCtxOk`'s `md`).
- **Merges** (the context-indexed predicate becomes the existing token-indexed one): `principalBound s M ctx`
  → `principalBoundT s M tok` (and `principalBoundI`), `hdrBoundM on s E ctx` → `hdrBoundT s E.authMode tok`
  gated by `on` (as `hdrBoundM` is), `infoBoundM` → `v3rpc.infoBoundT`, `ctxBoundOrTLS s M ctx` →
  `… tok`, `noPrincipalFrom M n ctx` → `… tok`, `tokRefusedFrom M n ctx` → `tokRefusedFrom tok`.
- **The request specs take the token:** `EtcdServer.{Put, DeleteRange, Txn, Range, LeaseGrant, LeaseRevoke,
  raftRequest, processInternalRaftRequestOnce}.spec` (7 `Spec/` files name `hdrBoundM … (ok ctx)`): `∀ … tok`,
  pre `□ (⌜E.authOn = true⌝ → auth.ctxToken ctx tok)`, `hdrBoundT … tok` in place of `hdrBoundM … ctx`. The
  auth-off theorems instantiate `tok := none` (premise vacuous: `E.authOn = false`), so their text is unchanged.
- **v3rpc:** `srvKVAnsOn`/`srvKVAnsM`'s `⌜on = true → auth.ctxTokenOf ctx = tok⌝` → `□ (⌜on = true⌝ →
  auth.ctxToken ctx tok)` (the tree already indexes the answers by `tok`); `lessorGrantOkGM`/`lessorRevokeOkM`,
  `ctrlP`, `swsIs`, `ctrlMid`, `userAddAnsOn` & co. take `tok`; `ReadWhy`'s `rangeWhy`/`txnWhy` by `tok`, and
  `rangeWhy_ctx`/`txnWhy_ctx` go.
- **Who supplies `ctxToken ctx tok` with auth on:** the handler, from `grpcAccepted`'s `ctxInMD ci md`
  (`tok := mdTokenOf md`), through `WithValue`/`Tracer.Start`/`ctxInMD_cancel`/`ctxInMD_cc` to the internal
  contexts (`txnCtx`, `srvCtxWeak`); in `.any` mode, callers with no run context take it from `libCtxOk`.

### 4.3 The examples' auth contract (review 2, m4)

`deliversOutgoing c h` (`incomingOf h = outgoingOf c`) and `userAttemptOk γa u h` are used only by
`badCtx_unbound` and its export `authkv_bad_unbound`. Revision 3 keeps the client-to-server link explicit:
`deliversOutgoing c h md := ⌜∃ hc, h = ok hc⌝ ∗ ctxInMD hc md ∗ ⌜outgoingOf c = md⌝` in this part (the outgoing
part, later, makes the last conjunct `outMD c md`), and `userAttemptOk γa u tok` by token. The theorem
(§7) says: the request whose handler context `h` carries the client context `c`'s outgoing metadata `md`, whose
`token` values are `[badToken]`, has no principal bound to the token it carries. **Said plainly for Q9:** its
logical content is "a bad token binds no auth info"; the `c`/`h` premises carry the link for the reader, not
for the proof (as today: the old statement also followed from the token alone, through `ctxTokenOf_bad`).

## 5. Why none of it transfers across heaps (incoming), and agreement

- **(a)** No entailment concludes a pure fact from `ctxInMD`, `incomingCtxOk`, `ctxToken` or the leaf (I2);
  the laws conclude relations. **(b)** A fresh world builds `ctxInMD x none` for a context of a foreign type
  (`ctxChain`'s foreign root admits any `Value` WP form, which a fresh world satisfies) and `ctxInMD x none`
  for `Background()`/`TODO()`-rooted chains; it builds no `ctxInMD x (some f)` (that needs the leaf
  `transportMDRaw`, I4). Nothing follows from what it builds: every pure fact sits in a triple's post
  (`FromIncomingContext`, `AuthInfoFromCtx`), vacuous there (review 2, m1: revision 2's "cannot build
  `ctxInMD`" was inaccurate; `ctxInMD` is a definition, constructible from it, and is not sealed).
  **(c)** No post of interpreted code concludes anything about incoming metadata but transfers (`WithCancel`
  & co. through the proved laws); the leaf has no interpreted producer (I4'; review 2, (5): grpc's `metadata`
  is names-only, `acceptRun`/`acceptRunConns` model-only names without an unfold).
- **Agreement (ledger entry 1, wording corrected after review 2, (3)).** `ctxInMD ctx o ∗ ctxInMD ctx o' ⊢ ⌜o =
  o'⌝` is **unprovable from the definitions** (a foreign root's `Value` WP form admits every result, and the
  leaves have no agreement) and **false in the intended model** (a context whose `Value` diverges carries both
  `none` and `some f`), yet **consistent as a Lean axiom** (interpret the leaf as `False`: `some` never
  derivable, grpc's producers vacuous). At another key a `valueCtx` continues the *chain*
  (`CtxValue.lean:90-94`); the WP form appears only at a foreign root, which any chain can reach. No proof
  needs it: the two consumers that seemed to are restated with one `md` from one producer (§3, §4.2, §4.3).
  SpecPlan uses it nowhere (no spec, no `examples/specreq` snippet: only its definition `Api.lean:923` and
  `notes/specs-only/integration-I3.md:65`): ledger entry 1 proposes deleting it (and `ctxPeerCN`'s half).

## 6. Probes (throwaway, not in the tree)

Checked with `cd /shared/etcd-grove-incomingof && lake --packages=/shared/tmp/manifest-6d3.json env lean
<file>` at `49bd7924e6`, **no errors, no `sorry`**:

- `/shared/tmp/perheap/Probe.lean` (revision 1; 13 s): `ctxInMD` (as `incomingIsP`) over `ctxValue`; the two
  refuted axioms' replacements as theorems (`incomingIsP_cancel`, 6 lines; `v3rpc.incomingIsP_cc`, 14 lines).
- **`/shared/tmp/perheap/ProbeAuth.lean`** (revision 3, ~330 lines, 28 s): the leaf with `hG` in its binders,
  `ctxInMDQ`, `ctxTokenIsQ` (= `auth.ctxToken`), `ctxBoundQ`/`noPrincipalFromQ`/`tokRefusedFromQ` by token,
  `FromIncomingContextQ.spec` restated;
  - `auth.authStore.AuthInfoFromCtxQ.wp_proof`: **the one spec proved** (today's `specLb` by token, metadata
    gated by `M.isOn`), adapted from `FreshCtx.lean`'s `wp_lb` (both key branches); the gate costs 6 lines
    (the `true` verdict excludes `.off`);
  - `spec_w`: today's weaker `.spec` shape **as a corollary** (floor `0`: `authPubLbM_zero`);
  - `spec_off`: **the auth-off instance needs no metadata at all** and returns `a = null` — what the chain of
    `range_linearizable` & co. needs from the store (their `EtcdServer.Range` call instantiates `tok := none`).
  Not probed: the EtcdServer-level merge (the TLS fallback reads `libCtxOk`'s anonymous `md`: no new reasoning)
  and the v3rpc callers (mechanical: `ctxTokenOf ctx` → the parameter `tok`).

## 7. Closed and exported statements (incoming part, complete)

Scan: every theorem statement in every `Results.lean`/`MainLinked.lean`/`Adequacy*.lean`/`Robust*.lean` under
`Proof/` and the parts (`/shared/tmp/perheap/scan4.py`), for the incoming vocabulary and every definition that
mentions it (the 63 definitions of `/shared/tmp/perheap/inc-defs.txt`).

**Closed statements (Adequacy/MainLinked/Robust): no text change, no new premise.** The trust base shrinks:
deleted axioms `incomingOf_cancelCtx`, `v3rpc.incomingOf_cancellableContext` (22 collections: auth3, authN,
authkv, cachekv, compactkv, k8scompactor, k8setcd3, leaseN, leasecatchup, leaseexpiry, leaseexpiryN, leasekv,
linkv3p, linkvtxn, m2, putget, putget3, putgetN, txnlinfaultsN, v3rpc, watch, watchkv); deleted opaques
`incomingOf`, `transportMD`; added opaque `transportMDRaw` (no law); restated trusted texts
`FromIncomingContext` (23 collections), `WithValue` (35), `Tracer.Start` (31), the model's `acceptRun`/
`acceptRunConns` posts (through `grpcAccepted`); meaning-only: `AuthInfoFromTLS`, `NewAuthStore`.

**Exported statements whose text changes (for approval, Q9):**

| statement | file:line | change |
|---|---|---|
| `put_end_to_endM`, `deleteRange_end_to_endM`, `range_end_to_endM`, `txn_end_to_endM` | `v3rpc/Results.lean:392, 442, 492, 552` | `auth.ctxTokenOf ctx` (in `srvKVAnsM …`, `kvDepOwnM …`, `writeGrantOn …`) → a new binder `(tok : Option GoString)`, and a new premise `□ (⌜E.authOn = true⌝ → auth.ctxToken ctx tok)`. Dischargeable and not vacuous: their users `etcd_putHandlerM` & co. (`client/v3/Results.lean:1194, 1375, 1543, 1880`) receive `ctxInMD ci md` from the handler contract (`tok := mdTokenOf md`); with auth off it is vacuous and `tok` is free (off, the answers' token rows are gated by `on`) |
| `authWrapOut_userAdd` | `v3rpc/Results.lean:856` | `userAddReplied … (auth.ctxTokenOf (ok ctx)) …` → the answer's token parameter: `authWrapOut (userAddAnsOn s E ρ ctx cd F tok name false Qa) resp err ⊢ authSlot s E ∗ (⌜err = nil⌝ -∗ userAddReplied s E ρ tok name Qa)` (no new premise: the token is the answer's) |
| `authkv_bad_unbound` | examples auth `Results.lean:123` | `(hd : deliversOutgoing c h) (ht : mdVals (outgoingOf c) "token" = [badToken]) : ctxBound (.on γa) h a ⊢ ⌜a = null⌝` → `(md : GrpcMd) (ht : mdVals md "token" = [badToken]) : deliversOutgoing c h md ∗ ctxBound (.on γa) (mdTokenOf md) a ⊢ ⌜a = null⌝` (§4.3) |

**Exported statements whose text is kept and meaning changes** (through redefined definitions; none gains a
conjunct a caller must newly discharge):

- `libCtxOk` (incoming part: `transportMD` → the leaf, as `∃ md, ctxInMD ctx md`): `range_linearizable`,
  `range_serializable`, `txn_readonly`, `txn_applied` (`etcdserver/Results.lean:652, 714, 774, 819`; review 2's
  MAJOR 2: **text kept**, §3); `ctxTraceIs_none_of_runCtx` (`client/v3/Results.lean:1172`, `grpcRunCtx`).
- the grpc contracts (`Spec md` at a received `ctxInMD ci md`): `etcd_cache_served` (`cache/v3/Results.lean:240`);
  in `client/v3/Results.lean`: `etcd_{put,range,delete,txn}HandlerM` (1194, 1375, 1543, 1880),
  `etcd_{put,range,delete,txn}MethodMd` (2214, 2243, 2274, 2303), `etcd_compactMethodM` (2334),
  `etcd_quotaHandler{,Own,Plain}_lent` (2401, 2413, 2425), `etcd_runOk(s)_of_slot` (2439, 2453),
  `etcd_kv_servedM_with` (2484), `etcd_kv_served(_with)` (2647, 2715), `etcd_kv_started(_with)` (3637, 3686),
  `etcd_leaseGrantMethodOk(Md)` (3927, 4022), `etcd_leaseRevokeMethodOk(Md)` (3967, 4002), `etcdGrpcSlot_eq`
  (4088), `srvRunOks_of_slot` (4163), `etcd_lease_served` (4195), `etcd_kv_lease_served` (4241),
  `client_lessor_isEtcdLease_served` (4300), `client_new_isEtcdLeaseClient_served` (4331); in
  `v3rpc/Results.lean`: `raftKV_serverM` (160, `srvKVAnsM`), `etcd_{userAdd,roleAdd,userGrantRole,
  roleGrantPermission,authEnable}HandlerOk` (927–1125), `…MethodOk` (1172–1300), `grpcHandlerOwnOkMd_frame`
  (1350), `watch_streamHandlerOk` (1745), `etcd_watchMethodOk` (1779), `etcd_watch_served(_chain)` (1865, 1964),
  `lessorGrantOkLiveM_server`, `lessorRevokeOkM_server` (2135, 2146).
- `watch_registered_authorized` (`v3rpc/Results.lean:1700`): already by token (`infoBoundT … tok`); unchanged.

## 8. Go evidence (incoming)

- `FromIncomingContext` reads `ctx.Value(mdIncomingKey{})`, asserts `MD`, copies (grpc
  `metadata/metadata.go:268-282`); `*cancelCtx`/`*timerCtx`/etcd's `cancellableContext` answer other keys as
  their parent (`examples/axiomcx/incomingof` `TestWrapperInheritsIncoming`, `TestIncomingNotConstant`;
  `examples/axiomcx/incomingof-attack`, re-run 2026-11-18: `ok`).
- The store's read only when enabled (`server/auth/store.go` `AuthInfoFromCtx`); the server's TLS fallback
  reads the metadata whatever the mode (`server/etcdserver/v3_server.go:1206-1216`, `store.go:1025-1069`, `:1044`).
- The transport's `MD`: built once in `operateHeaders`, handed to a tap handle after `NewIncomingContext`
  (`internal/transport/http2_server.go:543-575`). Step 1 adds a Go test (`examples/axiomcx/perheap/`) that etcd's
  server installs no tap handle and that a handler's `FromIncomingContext` copy is independent of the map.

## 9. Steps, estimates, checkpoints (step 0 + incoming)

Each lands on its own (`etc/land.sh` after the coordinator's go), in place (no twins: the two `AuthInfoFromCtx`
pairs merge).

| step | what | files (text edits) | lines (est., changed) | agent-days |
|---|---|---|---|---|
| 0 | Vocabulary (§2: leaf with `hG`, `incomingHeld`, `ctxInMD`, `incomingCtxOk` redefined, `auth.ctxToken`, `ctxBound` by token); the laws (the probe's two theorems in the tree, `_timer`, `_valueCtx`, `_from`, `_background`, `ctxInMD_valueAt`); the `HasLC.hasLC` move (~12 files, form); `libCtxOk`'s producers re-proved (incl. the 6 `_of_nil` users); Go test; ledger entry 1 decided | ~20 | 400 | 3–4 |
| 1a | **C1a, first**: the auth chain by token (§4.2): store and server `AuthInfoFromCtx` merged (the probe's proof in the tree), `isReqAuthBound`, the predicate merges, `ReqOn`/`AuthBound`/`AuthReqDerive`/`AuthSrv`/`AuthApplyOn`/`ReadWhy`, the checks (`requireAuthInfo`, `checkLease*`, `doSerialize`, `processInternalRaftRequestOnce`, `checkMembershipOperationPermission`), the 7 request specs with `tok`, the four auth-off theorems' proofs (`tok := none`) | ~66 | 1300 (−350 deleted twin proofs) | 7–9 |
| — | **C1a checkpoint**: the chain and the auth-off theorems `lean-check`ed; report (forms decided, measured cost) | | | |
| 1b | the rest (§4.1): delete `incomingOf` and the axioms; `FromIncomingContext`/`WithValue`/`Tracer.Start`/`EnsureTrace`; `grpcAccepted` and the contracts; `newStreamInterceptor` with the passed `md`; the 21 handler specs + 4 `LeaseServer` + `watchServer.Watch` and their proofs; v3rpc (`ServerKVOn`, `LeaseOn`, `InvWatch`, `sendLoop`, `SrvCtxWeakLaws`, Results); client Results (the handler theorems pass `ctxInMD`); examples auth (§4.3); otel/`net/http` stragglers | ~50 | 1300 | 6–8 |
| — | **C1**: full build; `tcb-report --check --update` (the two axioms gone from 22 collections; restated texts); interfaces regenerated (`etc/gen-interface.py` for raft, cache, server APIs touched); `notes/axiom-review/perheap-incoming.md` (each new trusted text against (a)/(b)/(c), I4', the P-i test); audit rows; stop, land | | | |
| all | merges of `lean`, two full builds (~12.8k modules, 45G slot, retries), collection baselines, interfaces, handoffs | | | 3–4 |

**Total: ~120 files, ~3000 lines changed, 19–25 agent-days: 4–5 weeks** (target 3–4: not met honestly; the auth
chain is 66 files, not revision 2's 38). 3.5 weeks is reachable only if C1a finds the request-spec changes
mechanical (one binder and one premise per spec, most proofs unchanged after a `tok := mdTokenOf md`).

## 10. Risks (incoming)

- **R1. A proof needs agreement after all** (two `ctxInMD` of one context, no call between, and the two `md`s
  must be equal). Stop: an agreement law needs its own review (§5). Mitigation: C1a covers the known consumers.
- **R2. `libCtxOk` producers without a chain.** `libCtxOk_of_nil` at one of `context`'s own types (not foreign)
  cannot give `ctxInMD`; each of its 6 users is checked in step 0 (expected: foreign types or `ctxValue` forms).
- **R3. The `HasLC.hasLC` move** hits a `{hlc}`-generic user that is instantiated elsewhere. None known (every
  caller is at `HasLC.hasLC`); found in step 0's build.
- **R4. Build cost and memory**: two full builds; `[∗list]`/`List.replicate` contexts framed explicitly.
- **R5. Interference** (shared grpc contracts, the auth chain): land soon after C1.
- **R6. SpecPlan divergence**: ledger entry 1 (agreement) pending; if the user keeps `ctxInMD_agree`, step 1
  needs revision 2's §2.3a opaque realization (two trusted transfer entailments, a model argument): +3–5 days
  and a separate review.

## 11. Open questions (incoming), each with a recommendation

- **Q2. Agreement law.** Recommend **none**; delete `ctxInMD_agree.spec` from `SpecPlan/` (ledger entry 1:
  unprovable from the definitions, false in the intended model, consistent as an axiom, used nowhere).
- **Q3. `ctxInMD` defined over the chain, at `HasLC.hasLC`.** Recommend yes (both refuted axioms become
  theorems); the ~12 `{hlc}`-generic files move to `HasLC.hasLC` (form). Alternative (not recommended): a
  `valueAt`-based twin for readers, the `libCtxOk`/`libCtxOkC` split again.
- **Q9. Exported statements** (§7): approve the three text changes (the four `*_end_to_endM` with `tok` and the
  gated premise; `authWrapOut_userAdd` at the answer's `tok`; `authkv_bad_unbound` with `md` and the explicit
  link, its content said plainly) and the meaning changes listed.
- **Q13. The auth chain by token, the twins merged.** Recommend: `ctxBound`/`noPrincipalFrom`/`tokRefusedFrom`
  by token; `principalBound`→`principalBoundT`, `hdrBoundM`→`hdrBoundT`, `infoBoundM`→`infoBoundT`; each
  `AuthInfoFromCtx` one spec (the `Lb` form) with the old form a corollary (probe).
- **Q14 (changed). Sources of a context's metadata.** Recommend: `libCtxOk` keeps the anonymous
  `incomingCtxOk = ∃ md, ctxInMD ctx md` (needed: the TLS fallback and `NewAuthStore`'s `isReqAuth`, §3); the
  `md` a spec is about comes only from `grpcAccepted`; specs relating metadata take `md`/`tok` as a parameter.
- **Q17 (new). The mode gate.** Recommend `□ (⌜M.isOn = true⌝ → auth.ctxToken ctx tok)` in the `AuthInfoFromCtx`
  and request specs (true of Go; the auth-off theorems keep their text). SpecPlan's
  `authStore.AuthInfoFromCtx.spec` takes `ctxToken ctx o` ungated, having no mode: in `.on`/`.any` the two
  coincide, so this is the mode's row, not a SpecPlan defect; no ledger entry (say if you want one).
- **Q15. Leaves with `hG`, (I4').** Recommend yes (probe: the leaf declared with `[hG : HeapGS HasLC.hasLC GF]`).

---

# Part II — errors and outgoing (outline; back to the user after Part I)

Revision 2's §1.2 (errors and outgoing rows), §1.3, §2.2, §3.2, §3.3 (commit `3b10ff2b93`) stand as the
outline; nothing there is decided beyond the directions below. Recorded for the later Scope:

- **Review 2, MAJOR 1 (`isSafeRetry` needs agreement on a pointer-typed status error; R2 occurred) —
  decided direction (a):** the invoker's post (`grpcInvokerOk`'s outcome) states that its error is a **fresh**
  `*status.Error`, unequal to the value of every `rpctypes` variable (true in Go: grpc's client builds the error
  from the received status; a pure fact about a returned value in an uninterpreted post, I3). `isSafeRetry`'s
  identity branch is then absurd. C2a converts `isSafeRetry`/`Client.unaryClientInterceptor` first (with
  `listReadError`, `shouldRefreshToken`, which close with the value pin).
- **Review 2, MAJOR 3 (B1's `descIs` obligations at ~12 call sites; the pin unprovable for errors of unknown
  type) — decided direction:** `errors.IsStatusErr`'s precondition as the disjunction `(descIs err m ∗ descIs
  target m') ∨ ⌜m = m'⌝` (callers ignoring the result supply the trivial side), or `∃ m, descIs err m` inside
  `statusErrOk` (its producers know the types); `descIs_of_errView` with a type premise
  (`∀ y, err ≠ mkOk EtcdError.ty #y`) or dropped. To be chosen in the errors Scope.
- **m3 (inventory):** `status.Status.Code.wp_proof` (`Proof/google_golang_org/grpc/status/Status__Code.lean:26`,
  spec `Spec/…/Status__Code.lean:31-35`, pre `grpcStatusRO s c`; users: `client/v3/leasing`'s `Code()`, k8s E1)
  is an axiom over names-only code; the errors part restates it (pre `□ statusAt s c m`, `s ≠ null`).
- **m2, m5:** the (I2) exemption for (I5) facts and the P-i test are in §0 (they apply to all parts).
- **Estimate (review 2):** the whole redesign 9.5–12 weeks; Part I is 4–5 of them; Part II's remaining steps
  (errors 12–16 days + MAJOR 1/3 design 5–9 days; outgoing 6–8 days; the rest of the family 2–3) are re-scoped
  when the user decides.

# H0 — withdrawn from this Scope

Revision 2's §5a (H0, the hot fix of F1) is withdrawn: by the user's decision of 2026-11-18 a separate
fmt-soundness branch lands `fmt.ErrorfWrap` restated and proved (review 2's H0′) with a term-level `Errorf` gate,
including review 2's consumer list (8 files: `apply/Base.lean:488-489, 531-532`, `cache/v3/Base.lean:951`,
`storeTxnCommon__rangeKeys.lean:699` added) and the `notes/decisions.md` supersession. Part II's errors steps
assume it has landed (`errDesc`'s only allocated-value conjunct is then a theorem's; F1 closed by construction).

---

## 12. Review 2, item by item

| item | answer |
|---|---|
| H0 verdict, H0′, fixes 1–4 | out of this Scope (the user's decision): the fmt-soundness branch (H0 section) |
| MAJOR 1 (`isSafeRetry`) | Part II: direction (a) recorded; C2a order |
| MAJOR 2 (auth-off callers, `specLb` twins) | §3 (gate adopted; `libCtxOk` keeps an anonymous incoming part: the TLS fallback, `NewAuthStore`), §4.2 (both pairs merged, probe), §7 (four auth-off theorems: text kept), Q13, Q14, Q17 |
| MAJOR 3 (`descIs` obligations, the pin) | Part II: direction recorded |
| m1 (§2.3 wording) | §5 (b) |
| m2 (I2 exemption) | §0 |
| m3 (`status.Status.Code`) | Part II |
| m4 (`authkv_bad_unbound`) | §4.3, §7 |
| m5 (P-i test) | §0; C1's per-text check |
| (3) `ctxInMD_agree` wording | §5; ledger entry 1 reworded |
| (4) `grpcAccepted` single source | §3 (single source of the `md` a spec is about), §4.1 |
| (6) §4 completeness | §7 (scan of every exported statement, with the definitions that mention the vocabulary) |
| (7) twins, estimate | §1, §4.2; §9 (4–5 weeks for Part I) |
