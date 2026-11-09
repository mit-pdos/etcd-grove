/-
# etcd's gRPC services (batch 2a): `server/v3/etcdserver/api/v3rpc`, all but `watch.go` (2b)

The handlers a member registers with grpc (`v3rpc.Server`): KV, Lease, Cluster, Auth,
Maintenance (and Watch, 2b's), their interceptors, the quota wrappers, the error mapping. This
file is the vocabulary their specs share, and the **realization of W0's `servesAt`**: a member
serves etcd at `ep` when `ep` is bound (grpc's `addrAt`) to **etcd's contracts** (`etcdContract γ`),
one per method, each the server's half of the client's shape (W0's `KV.*Triple`, 1c's `CallTriple`).

## The contract of a unary method (`etcdUnary γ m`)

A caller of method `m` hands over, with a request whose content models `rq` (`reqModels`, 3h's
decoding) and metadata the member authenticates as `who` (`mdPrin`, 2c/3d's slot), its update
`callAU γ who rq rep Q` (1c's: persistent if `rep`; a read's must be persistent, the member firing
it at the state it reads and possibly at earlier ones), and three ways to finish, one of which the
member takes (`∧`):

1. **answered**: the member fired the update with the answer `res` (`Step who rq σ σ' res`, a
   refusal included: `Step.refuse`), and sends the outcome `ansOutcome m res o` (the reply's content
   for `.ok b`, `replyModels`; a status with `e`'s description for `.err e`): the caller gets `Φ o`
   from `Q σ σ' res`;
2. **refused unfired**: a token refusal (`errRetryAuth`) or a learner's refusal, the update given
   back with the status (the client's interceptor resends or fires the refusal itself, 1c);
3. **unsettled**: a status that settles nothing (`indefMsg`: no description of a definite, mapped
   etcd error): `Φ` without the update (which the member may still fire: a write's entry may commit
   after the timeout).

This is W0's firing discipline (`req/..._api_v3rpc.md` item 3) in grpc's shape (`Grpc.UnarySpec`,
the urpc style W0 asked for): **at most once** for an exclusive update holds because the member
fires it only from the entry's apply (2c/2d), grpc runs a call's handler at most once per attempt
(`Grpc.attemptOk_call`), and the client resends only after (2), which fired nothing.

The maintenance RPCs that answer from the member and change no modelled state (`Status`, `Hash`,
`HashKV`, `Defragment`, `MoveLeader`, `Downgrade`) have `etcdLocal`: no update, any outcome.
Streams: `rangeStreamSpec γ` (this file), `kaSpec γ` (keep-alives: nothing modelled), `snapSpec`
(the backend's bytes: nothing modelled), `watchSpec γ` (1b's wire protocol; in the client's
`ApiWatch.lean` since integration X).

## Round 1 repairs (in brief)

* The contract is per member (`etcdContract γ ep`): the lease requests carry and give W0's
  `leaseViewLb γ ep` (`leaseFact`); `servesAt_addr` at `ep`.
* The first way fires only answers that are not a token or learner refusal (`firedAns`): those go
  back unfired (1c's `AttemptTriple`); 2c must not fire them at apply.
* A definite error's code is pinned (`code e`, or `Unknown` for the two `EtcdError`s).
* Reads compose with 2c's `SrvCallTriple` once W0's round 4 makes a read's permission checked at an
  auth state between the call's start and its answer (so 2c's `srvStep` is `Step`).
* The health service is in the contract (`etcdLocal`, a trivial stream), its handlers meet it
  (`healthRegs_ok`); `InitializeMetrics` (`metricsOk_init`).
* `srvErrOk` (what `togRPCError` takes; 2c's error outcomes give it).
* `rangeStreamSpec` admits `ErrCompacted` before the first chunk; `rsChunk_agree`, `rsChunk_hdr_last`.

## Integration I3 (2026-11-09)

* **3h's realizations** replace the slots: `reqModels`, `replyModels`, `chunkModels` are
  `EtcdServerPb`'s (definitions here, for the old names).
* **The caller's read window** (W0's rounds 4-6): `etcdUnary` and `rangeStreamSpec` carry the
  caller's `lo` with `authLb γ lo`, the update over `Step who rq σ σ' res lo` (`etcdAU`; 1c's
  `callAU` is its `lo = 0` instance, so 1c's `AttemptTriple` composes with `lo := 0`, `authLb γ 0`
  holding by its definition).
* **The principal**: `mdPrin γ md who` is introduced by the client (`mdPrin_of`, from W0's `ctxPrin`,
  the outgoing metadata and the credentials' `Credentials.credMD`, 1c's) and eliminated by the member
  (`reqPrin_of_md`: 2c's `reqPrin ctx who tls`, the certificate's name `tls` none or `who`, W0's
  one-identity-per-client scope, round 5). 2b's `srvCtxPrin` is `∃ tls, reqPrin ctx who tls`.
* **Composition with 2c's `SrvCallTriple`** (every handler over a server method): the handler holds
  `etcdAU γ who rq rep lo Q` and `authLb γ lo`, and hands 2c the update over `srvStep who tls rq σ σ'
  res lo`, built from its own: 2c fires it with `srvStep`, which is `Step who` here (the handler's
  check excludes `emptyRangeStep`'s empty key; `tls` is `none` or `who`, `reqPrin_of_md`; the answer
  fired: 2c's `srvStep_step`, I4); 2c's outcome 1 fires only `firedAns` answers (`firedAns` is 2c's
  `srvFiredAns`, I4/X: an apply-time token refusal is given back, outcome 2); outcome 2's update is
  the handler's again (the second way for a token refusal, else fired as a refusal or the third
  way); outcome 3 the third way. A transaction's checks give 2c's `txnChecked` (`txnCheck_checked`),
  hence 3b's `Txn.txnSafe` (2c's `txnChecked_safe`).
* `srvErrOk` **is 2c's `srvErrShape`** (`togRPCError`'s premise; two strengthenings of
  `srvErrShape` requested of I4: comparable errors, an unmapped message settling nothing).
* **The request's right** (I1's `reqRight γ rq`: W0's `urlsRight γ urls` for `MemberAdd`/
  `MemberUpdate`, `True` otherwise) travels with the request in `etcdUnary` to the member op (2e's
  `AddMember`/`UpdateMember` take it); it is spent whatever the outcome (not given back).
* A `Compact` request's revision is not `0` (2c's round-1 item 4: W0's client contract carries it;
  a raw gRPC client must too: the server's `Compact` would otherwise propose a compaction to `0`).
* `kaSpec`: a response's lease id is one the client sent (`kaReq`, `kaLog`: 1c's `kaSent`).
* `watchSpec` is a contract: the requests recorded (`wsReq`), each response a `wireStep` (1b) from
  the state the earlier ones made (`wsSt`), the stream's principal fixed (`wsWho`); 2b's server
  slots are opened from a run (`watchRun_open`).

## Integration X (2026-11-09)

* The two streams' contracts and their records moved to the client, which defines its names over
  them and cannot import this module (it imports the client): `kaSpec`, `kaReq`, `kaLog` (and
  `kaLog_alloc`, `kaLog_add`, `kaReq_lookup`, `kaReq_persistent`) to `client/v3/ApiLease.lean`, where
  1c's `kaSent g id` is `∃ i, kaReq g i id` and the halves take the stream's name `g`; `watchSpec`,
  `wsReq`, `wsSt`, `wsWho` (`watchSpec_records`) and the new request log `wsLog` (`wsLog_alloc`,
  `wsLog_add`, `wsLog_lb`) to `client/v3/ApiWatch.lean`, where 1b's `WatchStreamNames` is grpc's
  `StreamName` and `wireWatchSentLb g ss` is `[∗list] i ↦ r ∈ ss, wsReq g i r`. Still 2a's
  obligations (this file's names, `open ClientV3`).
* `credMD` is 1c's `Credentials.credMD` (a definition: no metadata, or a non-empty `tokFor` token),
  and the dial's `R` (`Credentials.rpcCredsAt_perRPC`).
* **2e's `srvGate`** (every request-path call of 2c's holds a share; `HardStop` takes the whole
  gate): grpc's runs now carry a run resource `T` (`Grpc.unaryOk`/`streamOk`/`regsOk`; `start` lends
  `n` copies with the thread tokens, `GracefulStop` gives them back, `drainTok`). `HandlerTriple`'s
  optional last argument is the run resource: every handler over a 2c method takes `srvGate s gq`
  (and returns it), the others `True`; `Server.spec` registers for any share; `icEtcdOk` passes `T`
  through. Open: `LeaseKeepAlive`'s loop outlives its run (its sketch), and the TLS path
  (`Grpc.startHTTP`) lends no run resource.
* `firedAns` is 2c's `srvFiredAns` (an abbreviation); 2c's `rsSink` has its send and context laws here
  (`rsSink_send`, `rsSink_context`), and `rsSink_intro` takes the run's context and `mdPrin`.
* Any context's incoming metadata and TLS peer (`Grpc.ctxInMD`, `ctxPeerCN`, `ctxCertUser`: 3d's
  provisional `Auth.*` names), with `rpcCtx_reqCtxOk` (4b) and `ctxNoIncoming_inMD` (2c's contexts).

## Vocabulary

* Pure: `etcdMethods`/`etcdStreams` (the method table: full names and message types),
  `ansOutcome`, `indefMsg`, `maxTxnOpsMax` (`4999`: `issues/etcd-txn-nested-depth-apply-panic.md`).
* **Names of other batches** (identified at integration): `reqModels m c rq`, `replyModels m b c`,
  `chunkModels c m` (3h's, definitions here), `mdPrin γ md who` (2a's own, opaque: a request with
  incoming metadata `md` is authenticated as `who`; introduced by `mdPrin_of`, eliminated by
  `reqPrin_of_md` into 2c's `EtcdServer.reqPrin`), `watchSpec γ`, `kaSpec γ` (2a's contracts, stated in
  the client's `ApiWatch`/`ApiLease`), `quotaOk` (2e's slot).
* Used from 2c (`Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiReq.lean`): `EtcdServer.isServer s γ`
  (the handle every server object here is over), `srvErrOf` (the server-side errors
  `togRPCError` maps), `SrvCallTriple` (the shape of the request path's methods), `txnChecked`.
* Ghost state of a streamed range: `rsReq g who r Q` (persistent, agreeing: the stream `g` carries
  the read `r` of `who` with `Q`; allocated by the client from grpc's `streamKey g`),
  `rsChunk g j m` (persistent: the `j`-th chunk sent is `m`). Intended realization: a ghost map
  from stream names, in the KV service's invariant.
* Handles (persistent): `kvServerAt p s γ` (`*kvServer`), `quotaKVAt q p s γ` (`*quotaKVServer`
  over it), `leaseServerAt`, `quotaLeaseAt`, `authServerAt`, `clusterServerAt`, `maintAt`
  (`*maintenanceServer`), `authMaintAt` (`*authMaintenanceServer`), `headerAt h s γ` (a `header`
  value), `authAdminAt aa s γ`, `quotaAlarmerAt qa s γ`, `notifierAt n`.

## Laws

`servesAt_addr` (W0's `servesAt` is `ep` bound to etcd's contracts), `rsReq_alloc`, `rsReq_agree`,
`handles_persistent`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Realize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch
public import Spec.go_etcd_io.etcd.client.v3.ApiLease
public import Spec.go_etcd_io.etcd.client.v3.credentials.Api
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Api
public import GeneratedProof.google_golang_org.grpc.health
public import GeneratedProof.google_golang_org.grpc.health.grpc_health_v1
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import GeneratedProof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

/-- The `--max-txn-ops` etcd's specs admit (`issues/etcd-txn-nested-depth-apply-panic.md`: above it a
nested transaction the gRPC check accepts can exceed protobuf's decoding depth at apply). -/
def maxTxnOpsMax : Nat := 4999

/-- **A status message that settles nothing**: no description of a definite etcd error that the
client maps (`Rpctypes.mapped`). -/
def indefMsg (msg : GoString) : Prop :=
  ∀ e : EtcdErr, Rpctypes.mapped e = true → msg = Rpctypes.desc e → e.indefinite = true

/-- The content `c` of a request of method `m` models `rq` (3h's `EtcdServerPb.reqModels`). -/
def reqModels (m : GoString) (c : Content) (rq : Req) : Prop := EtcdServerPb.reqModels m c rq

/-- The content `c` of a reply of method `m` carries the success body `b` (the reply's header
revision the body's; the other header fields any; 3h's `EtcdServerPb.replyModels`). -/
def replyModels (m : GoString) (b : RespBody) (c : Content) : Prop := EtcdServerPb.replyModels m b c

/-- The content `c` of a `RangeStreamResponse` carries the chunk `m` (3h's). -/
def chunkModels (c : Content) (m : RangeRespM) : Prop := EtcdServerPb.chunkModels c m

/-- **The outcome a member sends for the answer `res`** of a request of method `m`. -/
def ansOutcome (m : GoString) (rq : Req) (res : Resp) (o : Outcome) : Prop :=
  match rq, res with
  -- `LeaseTimeToLive` of a lease the lessor does not know is a reply (`lease.go:66-73`)
  | .leaseTimeToLive id _, .err .leaseNotFound =>
      ∃ c, o = .ok c ∧ replyModels m (.leaseTimeToLive id (-1) 0 []) c
  | _, .ok b => ∃ c, o = .ok c ∧ replyModels m b c
  | _, .err e => ∃ code, o = .status code (Rpctypes.desc e) ∧
      (code = Rpctypes.code e ∨ code = Grpc.cUnknown)

/-! ### The gRPC layer's validations, as the code computes them -/

open Classical in
/-- `checkRangeRequest`. -/
def rangeCheck (r : RangeReq) : Option EtcdErr :=
  if r.key = [] then some .emptyKey else if r.validSort then none else some .invalidSortOption

/-- `checkDeleteRequest`. -/
def deleteCheck (d : DeleteReq) : Option EtcdErr := if d.key = [] then some .emptyKey else none

/-- The first error of a list of checks. -/
def firstErr : List (Option EtcdErr) → Option EtcdErr
  | [] => none
  | some e :: _ => some e
  | none :: rest => firstErr rest

mutual
/-- `checkRequestOp(u, n)` (an empty operation is `ErrGRPCKeyNotFound`, the switch's default). -/
def opCheck (n : Int) : RequestOp → Option EtcdErr
  | .empty => some .keyNotFound
  | .range r => rangeCheck r
  | .put p => p.invalid
  | .deleteRange d => deleteCheck d
  | .txn cmps succ fail =>
      let opc : Int := max (max cmps.length succ.length) fail.length
      if n < opc then some .tooManyOps
      else if cmps.any (fun c => decide (c.key = [])) then some .emptyKey
      else
        match opsCheck (n - opc) succ with
        | some e => some e
        | none => opsCheck (n - opc) fail
def opsCheck (n : Int) : List RequestOp → Option EtcdErr
  | [] => none
  | op :: ops =>
      match opCheck n op with
      | some e => some e
      | none => opsCheck n ops
end

/-- **`checkTxnRequest(r, n)`**: the error it returns (`none`: `nil`). -/
def txnCheck (n : Int) (t : TxnReq) : Option EtcdErr := opCheck n (.txn t.compare t.success t.failure)

/-- **`checkIntervals(ops)` returns no error** (opaque: the puts and deletes of the operations,
recursively through nested transactions, have no key put twice in one branch nor a put inside a
delete's range, `key.go:217-309`, with the fork's fix of `issues/etcd-txn-delete-then-ignore-put.md`).
Its realization mirrors the code (a pure function over the key sets and the delete intervals). -/
opaque intervalsOk : List RequestOp → Prop

/-- **The checks' guarantee** to the request path: a transaction both checks accept at a budget of
at most `maxTxnOpsMax` is one the apply reads sequentially (2c's `txnChecked`) and nests within
protobuf's decoding limit (2c's `IrrBody.wf`: each level of `checkTxnRequest` costs at least one
operation of the budget, `notes/irr-depth.md`'s `txnCheck_msgDepth`). A law 2a proves. -/
def txnCheck_checked.spec : Prop := ∀ (n : Int) (t : TxnReq),
  n ≤ maxTxnOpsMax → txnCheck n t = none → intervalsOk t.success → intervalsOk t.failure →
  txnChecked t ∧ txnMsgDepth t + 1 ≤ 10000

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `monitorLeader`'s `*streamsMap` (persistent: its mutex guards the map of streams to cancel). -/
opaque streamsMapAt (sm : Loc) : IProp GF := iprop(True)

/-- A `*cancellableContext` over `parent` (persistent). -/
opaque cctxAt (c : Loc) (parent : GoInterface) : IProp GF := iprop(True)

/-- **A request with incoming metadata `md` is authenticated as `who`** (persistent; 2a's, realized
over 3d's auth store): its `token` (else `authorization`, `Bearer ` trimmed) a token the cluster
issued to `who` (W0's `tokenUser`), or no token and `who` the principal of the connections that send
`md` (`none`, or under `--client-cert-auth` their certificate's name); an invalid token is refused.
Every connection sending `md` has a client certificate naming `who` or none (W0's round-5 scope:
one identity per client, `connOk`'s premise): what `reqPrin_of_md`'s `tls` relies on.
Introduced by the client (`mdPrin_of`); eliminated by the member (`reqPrin_of_md`). -/
opaque mdPrin (γ : Cluster) (md : MD) (who : Principal) : IProp GF := iprop(True)

/-- **The client side of the principal**: a request sent with `ctx` (W0's `ctxPrin dflt ctx p`,
outgoing metadata `md0`) by a client of default principal `dflt` (credentials adding `mdc`: 1c's
`Credentials.credMD`, the connection's `R`) arrives
with metadata `md` (grpc's `mdSeen`) authenticated as `p`. -/
def mdPrin_of.spec : Prop := ∀ (γ : Cluster) (dflt p : Principal) (ctx : GoInterface)
    (md0 mdc md : MD),
  ctxPrin (GF := GF) dflt ctx p ∗ outMD ctx md0 ∗ Credentials.credMD γ dflt mdc ∗ ⌜mdSeen (md0 ++ mdc) md⌝ ⊢
    mdPrin γ md p

/-- **The member side of the principal** (2c's request, round 1, item 1): a run's context with
metadata authenticated as `who` has 2c's `reqPrin` of `who`, its certificate's name none or `who`
(`mdPrin`'s scope). -/
def reqPrin_of_md.spec : Prop := ∀ (γ : Cluster) (ctx : GoInterface) (md : MD) (who : Principal),
  rpcCtx (GF := GF) ctx md ∗ mdPrin γ md who ⊢
    ∃ tls : Principal, reqPrin ctx who tls ∗ ⌜tls = none ∨ tls = who⌝

/-- **A run's context is a request context the server's methods take** (4b's request,
`req/google_golang_org_grpc.md`, "from 4b"): no `traceutil` trace (grpc never sets etcd's
`TraceKey{}`), its otel span (set by the `otelgrpc` stats handler, or none) usable. -/
def rpcCtx_reqCtxOk.spec : Prop := ∀ ctx md, rpcCtx (GF := GF) ctx md ⊢ reqCtxOk ctx

/-- **The contexts without incoming metadata** (2c's `ctxNoIncoming`, the internal requesters') carry
none and no peer (3d's `AuthInfoFromCtx`/`AuthInfoFromTLS` on `s.ctx`). -/
def ctxNoIncoming_inMD.spec : Prop := ∀ ctx,
  ctxNoIncoming (GF := GF) ctx ⊢ ctxInMD ctx none ∗ ctxPeerCN ctx none

/-- **The update of a call by `p` with the read window `lo`** (W0's `Step`'s `lo`; persistent if
`rep`). 1c's `callAU` is `etcdAU … 0`. -/
def etcdAU (γ : Cluster) (p : Principal) (rq : Req) (rep : Bool) (lo : Nat)
    (Q : State → State → Resp → IProp GF) : IProp GF :=
  iprop(□?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p rq σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>)

/-- **The contract of etcd's unary method `m`** (see the header). -/
def leaseFact (γ : Cluster) (ep : GoString) (rq : Req) (vi : Option Nat) (σ σ' : State) (res : Resp) :
    IProp GF :=
  match rq with
  | .leaseGrant .. =>
      match res with
      | .ok _ => leaseViewLb γ ep (σ'.leaseTables.length - 1)
      | _ => iprop(True)
  | .leaseTimeToLive .. | .leaseLeases =>
      match vi with
      | some i => iprop(∃ j, ⌜i ≤ j ∧ σ.leaseAnsAt j rq res⌝ ∗ leaseViewLb γ ep j)
      | none => iprop(True)
  | _ => iprop(True)

/-- The answers a member sends fired (the first way): not a token refusal nor the learner's (which
1c's `AttemptTriple` needs back unfired, the second way). 2c's `srvFiredAns` (integration X: the same
body, identified), what 2c's outcome 1 gives. -/
abbrev firedAns (res : Resp) : Prop := srvFiredAns res

/-- **The contract of etcd's unary method `m` at the member serving `ep`** (see the header). The
lease requests carry the member's lease view (`leaseFact`, W0's `leaseViewLb γ ep`). -/
def etcdUnary (γ : Cluster) (ep : GoString) (m : GoString) : UnarySpec (GF := GF) :=
  fun md c Φ => iprop(∃ (who : Principal) (rq : Req) (rep : Bool) (Q : State → State → Resp → IProp GF)
      (vi : Option Nat) (lo : Nat),
    ⌜reqModels m c rq ∧ (rq.isRead = true → rep = true) ∧ (∀ r ph, rq = .compact r ph → r ≠ 0)⌝ ∗
    mdPrin γ md who ∗ authLb γ lo ∗
    reqRight γ rq ∗ etcdAU γ who rq rep lo Q ∗
    (match vi with | some i => leaseViewLb γ ep i | none => iprop(True)) ∗
    ((∀ (σ σ' : State) (res : Resp) (o : Outcome), ⌜firedAns res ∧ ansOutcome m rq res o⌝ -∗
        Q σ σ' res -∗ leaseFact γ ep rq vi σ σ' res -∗ Φ o) ∧
     (etcdAU γ who rq rep lo Q -∗ ∀ (e : EtcdErr) (code : w32),
        ⌜(errRetryAuth e = true ∨ e = .notSupportedForLearner) ∧ (code = Rpctypes.code e ∨ code = Grpc.cUnknown)⌝ -∗
        Φ (.status code (Rpctypes.desc e))) ∧
     (∀ (code : w32) (msg : GoString), ⌜indefMsg msg⌝ -∗ Φ (.status code msg))))

/-- **The contract of a member-local maintenance RPC**: no update; any outcome. -/
def etcdLocal : UnarySpec (GF := GF) := fun _ _ Φ => iprop(∀ o : Outcome, Φ o)

/-- **A streamed range's request is `r` of `who`, its update's result `Q`** (persistent). -/
opaque rsReq (g : StreamName) (who : Principal) (r : RangeReq) (Q : State → State → Resp → IProp GF) :
  IProp GF := iprop(True)

/-- **The `j`-th chunk of the streamed range `g` is `m`** (persistent). -/
opaque rsChunk (g : StreamName) (j : Nat) (m : RangeRespM) : IProp GF := iprop(True)

/-- **`RangeStream`'s contract**: the one request with the caller's persistent update (W0's
`RemoteKV.RangeStreamTriple`); each chunk recorded; the end: the update's `Q` with the answer the
chunks make (`streamMatches`), or a linearized error, or (after a chunk) `ErrCompacted` with no `Q`
(the pinned revision compacted between chunks), or a status that settles nothing. -/
def rangeStreamSpec (γ : Cluster) : StreamSpec (GF := GF) where
  up := fun g md i c => iprop(⌜i = 0⌝ ∗ ∃ (who : Principal) (r : RangeReq) (Q : State → State → Resp → IProp GF)
      (lo : Nat),
    ⌜reqModels go!"/etcdserverpb.KV/RangeStream" c (.range r)⌝ ∗ mdPrin γ md who ∗ rsReq g who r Q ∗
    authLb γ lo ∗ etcdAU γ who (.range r) true lo Q)
  dn := fun g _ j c => iprop(∃ m, ⌜chunkModels c m⌝ ∗ rsChunk g j m)
  fin := fun g _ n e => iprop(∃ (who : Principal) (r : RangeReq) (Q : State → State → Resp → IProp GF)
      (ms : List RangeRespM), rsReq g who r Q ∗ ⌜ms.length = n⌝ ∗ ([∗list] j ↦ m ∈ ms, rsChunk g j m) ∗
    match e with
    | none => ∃ (σ σ' : State) (rev : Nat) (a : RangeAns), Q σ σ' (.ok (.range rev a)) ∗
        ⌜streamMatches r ms rev a⌝
    | some (_, msg) => (∃ (σ σ' : State) (e : EtcdErr), Q σ σ' (.err e) ∗ ⌜msg = Rpctypes.desc e⌝) ∨
        ⌜msg = Rpctypes.desc .compacted⌝ ∨ ⌜indefMsg msg⌝)

/-- **`Snapshot`'s contract**: the backend's bytes, nothing modelled. -/
def snapSpec : StreamSpec (GF := GF) where
  up := fun _ _ _ _ => iprop(True)
  dn := fun _ _ _ _ => iprop(True)
  fin := fun _ _ _ _ => iprop(True)

/-- **A watch run opens 2b's server end** (2a's obligation, with 3h's `_Watch_Watch_Handler`'s
wrapper `x`, its points-to `GenericServerStream.mk st` held as grpc's `genSrvAt`): grpc's halves of a run of `watchSpec γ` are 2b's slots on the wrapper, for the
stream's principal and fresh names; the realization of 2b's slots is grpc's halves with the
records above (`srvWatchRecv_recv` from `srvRecv_recv` and `up`, `srvWatchSend_send` from
`srvSend_send` and `dn`, `srvWatchRecvdLb_sent` from `wsReq`). The end is `watchSpec`'s trivial
`fin` with 2b's error shape (`WatchServer.WatchTriple`). -/
def watchRun_open.spec : Prop := ∀ (γ : Cluster) (x : Loc) (ctx st : GoInterface) (md : MD)
    (g : StreamName),
  genSrvAt (GF := GF) x st go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty ∗
    rpcCtx ctx md ∗ srvCtxOf st ctx md ∗ srvRecv st g (watchSpec γ) md 0 ∗ srvSend st g (watchSpec γ) md 0 ⊢
  |==> ∃ (who : Principal) (gw : WatchStreamNames),
    srvWatchStreamAt (interface.mkOk (go.GoType.PointerType (google_golang_org.grpc.GenericServerStream.ty
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty)) #x)
      γ who gw ∗
    srvWatchRecv (interface.mkOk (go.GoType.PointerType (google_golang_org.grpc.GenericServerStream.ty
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty)) #x)
      gw [] ∗
    srvWatchSend (interface.mkOk (go.GoType.PointerType (google_golang_org.grpc.GenericServerStream.ty
      go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty)) #x)
      γ who gw WireSt.init

/-- **etcd's contracts** at a member's client address: every unary method of the KV, Lease,
Cluster, Maintenance and Auth services, and the four streams. -/
def etcdContract (γ : Cluster) (ep : GoString) : AddrContract (GF := GF) where
  unary := fun m =>
    if False then none
  else if m = go!"/etcdserverpb.KV/Range" then some (go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.RangeResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.KV/Put" then some (go_etcd_io.etcd.api.v3.etcdserverpb.PutRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.KV/DeleteRange" then some (go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.KV/Txn" then some (go_etcd_io.etcd.api.v3.etcdserverpb.TxnRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.KV/Compact" then some (go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Lease/LeaseGrant" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Lease/LeaseRevoke" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Lease/LeaseTimeToLive" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Lease/LeaseLeases" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Cluster/MemberAdd" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberAddRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberAddResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Cluster/MemberRemove" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberRemoveRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberRemoveResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Cluster/MemberUpdate" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberUpdateRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberUpdateResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Cluster/MemberList" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberListRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberListResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Cluster/MemberPromote" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberPromoteRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberPromoteResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Maintenance/Alarm" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AlarmRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AlarmResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Maintenance/Status" then some (go_etcd_io.etcd.api.v3.etcdserverpb.StatusRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.StatusResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/Defragment" then some (go_etcd_io.etcd.api.v3.etcdserverpb.DefragmentRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.DefragmentResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/Hash" then some (go_etcd_io.etcd.api.v3.etcdserverpb.HashRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.HashResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/HashKV" then some (go_etcd_io.etcd.api.v3.etcdserverpb.HashKVRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.HashKVResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/MoveLeader" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MoveLeaderRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MoveLeaderResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/Downgrade" then some (go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Auth/AuthEnable" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthEnableRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthEnableResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/AuthDisable" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthDisableRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthDisableResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/AuthStatus" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthStatusRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthStatusResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/Authenticate" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/UserAdd" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserAddRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserAddResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/UserGet" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGetRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGetResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/UserList" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserListRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserListResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/UserDelete" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserDeleteRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserDeleteResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/UserChangePassword" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserChangePasswordRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserChangePasswordResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/UserGrantRole" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGrantRoleRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGrantRoleResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/UserRevokeRole" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserRevokeRoleRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserRevokeRoleResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/RoleAdd" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleAddRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleAddResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/RoleGet" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGetRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGetResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/RoleList" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleListRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleListResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/RoleDelete" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleDeleteRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleDeleteResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/RoleGrantPermission" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGrantPermissionRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGrantPermissionResponse.ty, etcdUnary γ ep m)
  else if m = go!"/etcdserverpb.Auth/RoleRevokePermission" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleRevokePermissionRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleRevokePermissionResponse.ty, etcdUnary γ ep m)
    else if (∃ h ∈ healthMethods, h.1 = m) then
      some (google_golang_org.grpc.health.grpc_health_v1.HealthCheckRequest.ty,
        google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse.ty, etcdLocal)
    else none
  stream := fun m =>
    if False then none
  else if m = go!"/etcdserverpb.KV/RangeStream" then some (go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.RangeStreamResponse.ty, rangeStreamSpec γ)
  else if m = go!"/etcdserverpb.Watch/Watch" then some (go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty, watchSpec γ)
  else if m = go!"/etcdserverpb.Lease/LeaseKeepAlive" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse.ty, kaSpec γ)
  else if m = go!"/etcdserverpb.Maintenance/Snapshot" then some (go_etcd_io.etcd.api.v3.etcdserverpb.SnapshotRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.SnapshotResponse.ty, snapSpec)
    else if (∃ h ∈ healthStreams, h.1 = m) then
      some (google_golang_org.grpc.health.grpc_health_v1.HealthCheckRequest.ty,
        google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse.ty, snapSpec)
    else none

/-- **W0's `servesAt`, realized**: `ep` is bound to etcd's contracts. -/
def servesAt_addr.spec : Prop := ∀ (γ : Cluster) (ep : GoString),
  servesAt (GF := GF) γ ep ⊣⊢ addrAt ep (etcdContract γ ep)

/-- A chunk is recorded up to its header's ids (`headerFillingRangeStream.Send` fills them after the
server's request path recorded it). -/
def rsChunk_ids.spec : Prop := ∀ g j (m m' : RangeRespM),
  m.kvs = m'.kvs → m.more = m'.more → m.count = m'.count →
  m.hdr.map (·.revision) = m'.hdr.map (·.revision) → (m.hdr = none ↔ m'.hdr = none) →
  rsChunk (GF := GF) g j m ⊢ rsChunk g j m'

/-- Two records of one chunk agree, up to the header's ids (the ids are the only fields
`headerFillingRangeStream.Send` writes after the request path recorded the chunk). -/
def rsChunk_agree.spec : Prop := ∀ g j (m m' : RangeRespM),
  rsChunk (GF := GF) g j m ∗ rsChunk g j m' ⊢
    ⌜m.kvs = m'.kvs ∧ m.more = m'.more ∧ m.count = m'.count ∧
      m.hdr.map (·.revision) = m'.hdr.map (·.revision) ∧ (m.hdr = none ↔ m'.hdr = none)⌝

/-- **The chunk with a header is the last one sent** (`EtcdServer.RangeStream` puts the header on
the final chunk only). -/
def rsChunk_hdr_last.spec : Prop := ∀ g j j' (m m' : RangeRespM),
  rsChunk (GF := GF) g j m ∗ ⌜m.hdr ≠ none⌝ ∗ rsChunk g j' m' ⊢ ⌜j' ≤ j⌝

/-- **A server error `togRPCError` can take**: 2c's `srvErrShape` (integration I3: identified; was
2a's own predicate, round 1, provability F6). `togRPCError`'s proof needs two facts `srvErrShape`
does not state yet (requested of I4): a mapped leaf and an unmapped error are comparable (`cmpErr`:
the `toGRPCErrorMap` lookup), and an unmapped error's message settles nothing (`indefMsg`). -/
abbrev srvErrOk (err : GoInterface) : IProp GF := srvErrShape err

/-- **Slot (2e)**: a `storage.Quota` value (its `Available(r)` returns a boolean, no panic). -/
opaque quotaOk (q : GoInterface) : IProp GF := iprop(True)

/-- **grpc-prometheus's `*ServerMetrics`** (assumed: its interceptors call the handler once with
their own arguments and return its results; their counters write nothing the specs model). -/
opaque metricsOk (m : Loc) : IProp GF := iprop(True)

/-- **A unary server interceptor preserving etcd's contracts** (persistent): for each method `m`
etcd serves, with a continuation meeting the run's triple for `m`'s contract, calling the
interceptor meets it too (it refuses only with statuses the contract allows: an indefinite one, or
the learner's refusal with the update given back), the run's resource `T` passed through. -/
def icEtcdOk (i : GoFunc) (γ : Cluster) : IProp GF :=
  iprop(□ ∀ (T : IProp GF) (ep m : GoString) (reqT repT : go.GoType) (S : UnarySpec (GF := GF)),
    ⌜(etcdContract γ ep).unary m = some (reqT, repT, S)⌝ -∗
    ∀ (ctx : GoInterface) (md : MD) (q : Loc) (c : Content) (Φ : Outcome → IProp GF) (info : Loc)
      (k : val) (Ψ : val → IProp GF),
    (□ ∀ Ψ' : val → IProp GF, threadTok ∗ T ∗ rpcCtx ctx md ∗ msgAt reqT q (DFrac.own 1) c ∗
        Proto.decodedAt reqT q ∗ ⌜depth c < depthMax⌝ ∗ S md c Φ ∗
        (∀ (r err : GoInterface), threadTok -∗ T -∗ unaryOut repT r err Φ -∗ Ψ' (PairV #r #err)) -∗
      WP (App (App (Val k) (Val #ctx)) (Val #(msgVal reqT q))) {{ Ψ' }}) -∗
    threadTok ∗ T ∗ rpcCtx ctx md ∗ msgAt reqT q (DFrac.own 1) c ∗ Proto.decodedAt reqT q ∗
      ⌜depth c < depthMax⌝ ∗ info.[google_golang_org.grpc.UnaryServerInfo, go!"FullMethod"] ↦□ m ∗ S md c Φ ∗
      (∀ (r err : GoInterface), threadTok -∗ T -∗ unaryOut repT r err Φ -∗ Ψ (PairV #r #err)) -∗
    WP (App (App (App (App (Val #i) (Val #ctx)) (Val #(msgVal reqT q))) (Val #info)) (Val k)) {{ Ψ }})

/-- **A stream server interceptor preserving etcd's stream contracts** (persistent; the same for
streams: it calls the handler once with the stream, possibly wrapped with a context canceled when
the member loses its leader, or refuses with an indefinite status). Intended realization: the
analogue of `icEtcdOk` over `Grpc.streamOk`'s run. -/
opaque sicEtcdOk (i : GoFunc) (γ : Cluster) : IProp GF := iprop(True)

/-- A `*headerFillingRangeStream` at `w` over the stream `rs` with the header at `hp` (read-only). -/
opaque hfAt (w : Loc) (rs : GoInterface) (hp : Loc) (s : Loc) (γ : Cluster) : IProp GF := iprop(True)

/-- **A sink of the stream `g`** (persistent; `rsSink_intro`'s): which stream the sink sends on. -/
opaque rsSinkOf (w : GoInterface) (g : StreamName) : IProp GF := iprop(True)

/-- **2c's send end of a streamed range, realized** (2c's `rsSink rs γ p tls r ms`, `ApiReq.lean`):
the wrapper `w` (a `*headerFillingRangeStream` over the run's stream, `hfAt`) with the send half of
the stream `g` whose request is `r` of `who` (`rsReq`) is a sink with nothing sent, for the
connection's TLS principal (the run's context with `reqPrin` of `who`, `reqPrin_of_md`: integration X,
for `rsSink_context`). Its send law (2c's request): a chunk sent is recorded (`rsChunk g j m`,
`rsSink_send`). -/
def rsSink_intro.spec : Prop := ∀ (w : Loc) (rs : GoInterface) (hp : Loc) (s : Loc) (γ : Cluster)
    (g : StreamName) (md : MD) (who : Principal) (r : RangeReq) (Q : State → State → Resp → IProp GF)
    (ctx : GoInterface),
  hfAt w rs hp s γ ∗ srvSend rs g (rangeStreamSpec γ) md 0 ∗ rsReq g who r Q ∗ srvCtxOf rs ctx md ∗
    mdPrin γ md who ⊢
    ∃ tls : Principal,
    rsSink (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.headerFillingRangeStream.ty) #w)
      γ who tls r [] ∗
    rsSinkOf (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.headerFillingRangeStream.ty) #w) g

/-- **The sink's end** (what the handler returns, with what 2c's `RangeStream` gives at its
return: the update's `Q` and `streamMatches` of the chunks sent for `nil`; for an error, a
linearized error, `ErrCompacted`, or one that settles nothing) is the run's `streamOut`. -/
def rsSink_out.spec : Prop := ∀ (w : GoInterface) (γ : Cluster) (who tls : Principal) (r : RangeReq)
    (Q : State → State → Resp → IProp GF) (ms : List RangeRespM) (err : GoInterface)
    (rs : GoInterface) (g : StreamName) (md : MD),
  rsSink (GF := GF) w γ who tls r ms ∗ rsSinkOf w g ∗ rsReq g who r Q ∗
    (if decide (err = GoInterface.nil) then
       iprop(∃ (σ σ' : State) (rev : Nat) (a : RangeAns), Q σ σ' (.ok (.range rev a)) ∗
         ⌜streamMatches r ms rev a⌝)
     else iprop(∃ code msg, sentStatus err code msg ∗
       ((∃ σ σ' e, Q σ σ' (.err e) ∗ ⌜msg = Rpctypes.desc e⌝) ∨ ⌜msg = Rpctypes.desc .compacted⌝ ∨
        ⌜indefMsg msg⌝))) ⊢
  streamOut rs g (rangeStreamSpec γ) md err

/-- **The sink's send** (2c's request, round 1 item 3; integration X: what 2c's `RangeStream` calls on
the `KV_RangeStreamServer` value it is given): a chunk message modelled by `m` (owned; the sink fills
the header's ids, so the content after is some other) is sent and recorded, or the stream fails with
an error grpc made itself, nothing recorded. No `Q` travels with a chunk. Realized by
`headerFillingRangeStream.Send.spec` over `rsSink_intro`'s sink. -/
def rsSink_send.spec : Prop := ∀ (rs : GoInterface) (γ : Cluster) (p tls : Principal) (r : RangeReq)
    (ms : List RangeRespM) (resp : Loc) (c : Content) (m : RangeRespM),
  {{ rsSink (GF := GF) rs γ p tls r ms ∗
      msgAt go_etcd_io.etcd.api.v3.etcdserverpb.RangeStreamResponse.ty resp (DFrac.own 1) c ∗ ⌜chunkModels c m⌝ }}
    (App (Val (rs @!! go_etcd_io.etcd.api.v3.etcdserverpb.KV_RangeStreamServer.ty @!! go!"Send")) (Val #resp))
  {{ (err : GoInterface), RET #err;
      (∃ c', msgAt go_etcd_io.etcd.api.v3.etcdserverpb.RangeStreamResponse.ty resp (DFrac.own 1) c') ∗
      ((⌜err = GoInterface.nil⌝ ∗ rsSink rs γ p tls r (ms ++ [m])) ∨ (ownErr err ∗ rsSink rs γ p tls r ms)) }}

/-- **The sink's context** (integration X): the run's context, a request context of 2c's
(`rpcCtx_reqCtxOk`) whose principal pair is the sink's (`reqPrin_of_md` at `rsSink_intro`). -/
def rsSink_context.spec : Prop := ∀ (rs : GoInterface) (γ : Cluster) (p tls : Principal) (r : RangeReq)
    (ms : List RangeRespM),
  {{ rsSink (GF := GF) rs γ p tls r ms }}
    (App (Val (rs @!! go_etcd_io.etcd.api.v3.etcdserverpb.KV_RangeStreamServer.ty @!! go!"Context")) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; rsSink rs γ p tls r ms ∗ Context.ctxOk ctx ∗ reqCtxOk ctx ∗
      reqPrin ctx p tls }}

/-- A streamed range's parameters, fixed by the client with the stream's key. -/
def rsReq_alloc.spec : Prop := ∀ g who r (Q : State → State → Resp → IProp GF),
  streamKey (GF := GF) g ⊢ |==> rsReq g who r Q

def rsReq_agree.spec : Prop := ∀ g who who' r r' (Q Q' : State → State → Resp → IProp GF),
  rsReq (GF := GF) g who r Q ∗ rsReq g who' r' Q' ⊢ ⌜who = who' ∧ r = r'⌝ ∗ ▷ (∀ σ σ' res, Q σ σ' res ≡ Q' σ σ' res)

/-! ### Handles of the service objects -/

/-- A `*kvServer` over the server `s` (`NewKVServer`'s: its header of `s`, `kv` the server, `aa`
over it, `maxTxnOps` at most `maxTxnOpsMax`). -/
opaque kvServerAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
/-- A `*quotaKVServer` `q` wrapping the `KVServer` value `kv` (a `*kvServer`'s) over `s`. -/
opaque quotaKVAt (q : Loc) (kv : GoInterface) (s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque leaseServerAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque quotaLeaseAt (q : Loc) (ls : GoInterface) (s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque authServerAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque clusterServerAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
/-- A `*maintenanceServer` over `s` (`NewMaintenanceServer`'s inner value). -/
opaque maintAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
/-- An `*authMaintenanceServer` (the registered maintenance value). -/
opaque authMaintAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
/-- A `header` value of `s` (cluster and member ids, the raft status getter, the revision). -/
opaque headerAt (h : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header) (s : Loc) (γ : Cluster) :
  IProp GF := iprop(True)
opaque authAdminAt (aa : Loc) (s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque quotaAlarmerAt (qa : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaAlarmer) (s : Loc)
  (γ : Cluster) : IProp GF := iprop(True)
/-- A `notifier` (the health notifier) value. -/
opaque notifierAt (n : GoInterface) : IProp GF := iprop(True)

/-- **grpc-prometheus's interceptors pass through** (assumed; `getServerMetrics`' value). -/
def metricsOk_unary.spec : Prop := ∀ (m : Loc) (γ : Cluster),
  {{ metricsOk (GF := GF) m }}
    (App (Val (m @!! go.GoType.PointerType github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics.ty
      @!! go!"UnaryServerInterceptor")) (Val #()))
  {{ (i : GoFunc), RET #i; icEtcdOk i γ }}

def metricsOk_stream.spec : Prop := ∀ (m : Loc) (γ : Cluster),
  {{ metricsOk (GF := GF) m }}
    (App (Val (m @!! go.GoType.PointerType github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics.ty
      @!! go!"StreamServerInterceptor")) (Val #()))
  {{ (i : GoFunc), RET #i; sicEtcdOk i γ }}

/-- **grpc's health handlers meet their contracts** (assumed, grpc's own code: `Check`, `List`
answer from the health server's map; `Watch` sends statuses; nothing modelled), under any chain of
interceptors that preserve etcd's contracts. -/
def healthRegs_ok.spec : Prop := ∀ (γ : Cluster) (ep : GoString) (B : SrvCfg) (hs : Loc) (T : IProp GF),
  healthAt (GF := GF) hs ∗ ([∗list] i ∈ B.ics, icEtcdOk (GF := GF) (sem := sem) i γ) ∗ ([∗list] i ∈ B.sics, sicEtcdOk i γ) ∗
    regsOk B (etcdContract γ ep) T ⊢
  regsOk { B with
    regs := B.regs ++ healthMethods.map (fun h => (h.1, h.2,
      interface.mkOk (go.GoType.PointerType google_golang_org.grpc.health.Server.ty) #hs)),
    sregs := B.sregs ++ healthStreams.map (fun h => (h.1, h.2,
      interface.mkOk (go.GoType.PointerType google_golang_org.grpc.health.Server.ty) #hs)) }
    (etcdContract γ ep) T

/-- **`InitializeMetrics(gs)`** (grpc-prometheus, assumed: it reads `gs.GetServiceInfo()` and zeroes
its counters): the server being built is unchanged. -/
def metricsOk_init.spec : Prop := ∀ (m gs : Loc) (B : SrvCfg),
  {{ metricsOk (GF := GF) m ∗ srvBuild gs B }}
    (App (Val (m @!! go.GoType.PointerType github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics.ty
      @!! go!"InitializeMetrics")) (Val #gs))
  {{ RET #(); srvBuild gs B }}

def handles_persistent.spec : Prop :=
  (∀ p s γ, Persistent (kvServerAt (GF := GF) p s γ)) ∧
  (∀ q kv s γ, Persistent (quotaKVAt (GF := GF) q kv s γ)) ∧
  (∀ p s γ, Persistent (leaseServerAt (GF := GF) p s γ)) ∧
  (∀ q l s γ, Persistent (quotaLeaseAt (GF := GF) q l s γ)) ∧
  (∀ p s γ, Persistent (authServerAt (GF := GF) p s γ)) ∧
  (∀ p s γ, Persistent (clusterServerAt (GF := GF) p s γ)) ∧
  (∀ p s γ, Persistent (maintAt (GF := GF) p s γ)) ∧
  (∀ p s γ, Persistent (authMaintAt (GF := GF) p s γ)) ∧
  (∀ h s γ, Persistent (headerAt (GF := GF) h s γ)) ∧
  (∀ aa s γ, Persistent (authAdminAt (GF := GF) aa s γ)) ∧
  (∀ qa s γ, Persistent (quotaAlarmerAt (GF := GF) qa s γ)) ∧
  (∀ n, Persistent (notifierAt (GF := GF) n)) ∧
  (∀ w rs hp s γ, Persistent (hfAt (GF := GF) w rs hp s γ)) ∧
  (∀ sm, Persistent (streamsMapAt (GF := GF) sm)) ∧
  (∀ c p, Persistent (cctxAt (GF := GF) c p)) ∧
  (∀ m, Persistent (metricsOk (GF := GF) m)) ∧
  (∀ q, Persistent (quotaOk (GF := GF) q)) ∧
  (∀ γ md who, Persistent (mdPrin (GF := GF) γ md who)) ∧
  (∀ g j m, Persistent (rsChunk (GF := GF) g j m)) ∧
  (∀ g who r Q, Persistent (rsReq (GF := GF) g who r Q)) ∧
  (∀ w g, Persistent (rsSinkOf (GF := GF) w g))

/-! ### The shape of a unary handler's spec -/

/-- **A unary handler `f` of method `m`** (a service method `(ctx, req) → (resp, err)`, `P` its
receiver's handle): a run with the thread's token, the run's context, the request (owned: grpc
decoded it for this run) and the method's contract returns the token and `unaryOut`. Its instance at
the registered service value is what `Grpc.start` needs of each registration (with the generated
handler's decoding, 3h). `T` is what the run holds besides its thread's token and gives back
(integration X): a handler over 2c's request path takes the `srvGate s q` share grpc's `start`
lends each run (`Grpc.unaryOk`'s run resource; `Server.spec` registers for any share), the others
nothing (`True`; framed with the run's resource where they are registered). The request is a
decoded one (`Proto.decodedAt`, grpc's `decOk_call`: its range ends `nil` or non-empty, 3h's
`EtcdServerPb.endsDecoded`, what 2c's `Range`/`RangeStream`/`Txn` take). -/
def HandlerTriple (f : val) (P : IProp GF) (S : UnarySpec (GF := GF)) (reqT repT : go.GoType)
    (T : IProp GF := iprop(True)) : Prop :=
  ∀ (ctx : GoInterface) (md : MD) (q : Loc) (c : Content) (Φ : Outcome → IProp GF),
  {{ P ∗ threadTok ∗ T ∗ rpcCtx ctx md ∗ msgAt reqT q (DFrac.own 1) c ∗ Proto.decodedAt reqT q ∗
      ⌜depth c < depthMax⌝ ∗ S md c Φ }}
    (App (App (Val f) (Val #ctx)) (Val #q))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗ T ∗
      unaryOut repT (msgVal repT resp) err Φ }}

end res

end V3rpc
end EtcdGrove
end Perennial
