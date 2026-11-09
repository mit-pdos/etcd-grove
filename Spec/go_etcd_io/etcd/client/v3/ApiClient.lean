/-
# etcd's Go client: lifecycle, auth, cluster, maintenance, the interceptors (batch 1c)

The vocabulary batch 1c adds to W0's (`Api.lean`): the contracts behind W0's slots `authAt`,
`clusterAt`, `maintAt` (bundles of their methods' triples, in the KV contract's shape), the
configuration `New` takes (`cfgOk`), the principal a configuration names (`cfgPrincipal`), the
retry interceptor's contract, which is what makes W0's update shapes sound (`AttemptTriple`,
`uiOk`), the readiness of a client (`clientReady`), its endpoints (`epsTok`) and the in-process
client (`clientBare`). The lease contract (`leaseAt`) is in `ApiLease.lean`.

## The shape of every non-KV call (`CallTriple`)

As W0's KV contract (round 3): a call by a client whose credentials name `who`, sent with a
context carrying the principal `p` (`ctxPrin who ctx p`: `p = who` for a context with no metadata
of its own), takes the caller's atomic update over `etcdState γ` for the request `rq`
(`Model.lean`'s `Req`), fired by `Step p rq`, and returns either the answer's reply (`ansReply`: the
reply message for `.ok b`, `errVal e` for `.err e`) with the caller's `Q`, or an error that settles
nothing (`indefCall`). The update is **persistent** (`□`) exactly when the client's retry wrapper
marks the RPC repeatable (`reqRetryRep`: `retry.go`'s `withRepeatablePolicy()`), whether or not
the request writes: the interceptor then resends it after an `Unavailable` error, which may follow
an attempt that was applied, so the cluster may fire the update more than once (**a lease grant
may grant two leases, a revoke may answer `ErrLeaseNotFound` for a lease this very call revoked**:
the program's invariant sees every firing, the caller gets the last one's `Q`). Every other RPC's
update is exclusive and fired at most once.

## The retry interceptor's contract (what W0's at-most-once rests on)

`Client.unaryClientInterceptor` is installed on the client's connection; every unary call (the
generated stubs' `cc.Invoke`) runs it around grpc's own one-attempt invoker. The two contracts:

* `AttemptTriple inv cc` (**what grpc's invoker gives, 2a**, on a connection `grpcConnAt cc`): one
  attempt of a unary call (`unaryArgs`: the method, its request message modelled by `rq`, the reply
  holder) returns (1) success, the update fired; (2) a definite etcd error, the update fired with
  it; (3) an error after which the request is known **not applied**, the update **given back
  unfired**: not sent (`CallErr.notSent`), a token refusal (`errRetryAuth`: `ErrInvalidAuthToken`,
  `ErrAuthOldRevision`, `ErrUserEmpty`), or a learner's refusal (`.notSupportedForLearner`); or (4)
  another indefinite error (never `.notSent`), the update possibly fired later (lost to the caller).
* `uiOk ui c γ who` (the interceptor's, proved by `Client.unaryClientInterceptor.spec`): for any
  invoker meeting `AttemptTriple`, on a ready client (`clientReady c`: its token refresh reads
  `c.Auth`), the interceptor's call returns (1) or (2), or an indefinite error, never (3): it
  resends only after (3) (or, for a repeatable RPC, after an `Unavailable` or a timeout of the
  attempt, the update being persistent), refreshing the token first after a token refusal; when it
  gives up after (3) it **fires the update itself** with that refusal (every such error is
  `EtcdErr.refusal`), and when the refresh fails it fires it with the refresh's error (a refusal:
  `ErrAuthFailed`, ...) or returns an indefinite one. A caller's own interceptor that calls the
  invoker at most once (the gRPC proxy's) also meets the post: the refusal is fired by a ghost step.

So a non-repeatable write is applied at most once per call: it is resent only after an attempt
that applied nothing.

## Readiness (`clientReady c`)

`newClient` builds the client's members (`NewCluster`, `NewKV`, `NewLease`, ...) from the
connection before it sets `c.Auth`; a call through a member then would, on a token refusal, refresh
the token through a `nil` `Auth` and panic. No call is made then, so the specs make the window
explicit: `clientReady c` (persistent) is minted by `newClient` once `c.Auth` is set (and by
`clientBare_assemble` for an in-process client); the interceptor laws (`uiOk_call`, `siOk_call`)
take it, and so do the bundle introductions of the handles the members' constructors return
(`authHandle_authAt`, `lessorHandle_leaseAt`, ...: each handle records its client `c`; a handle
over a caller's remote records `null`, `clientReady_null`). The constructors themselves do not
need it. W0's `kvHandle_kvAt` needs the same premise (`req/go_etcd_io_etcd_client_v3.md`, from 1c).

## Endpoints (`epsTok c dq eps`)

`Client.dial` reads `c.endpoints[0]` without `epMu` and without an emptiness check
(`issues/etcd-client-dial-empty-endpoints.md`): every dial after `New` (`Client.Dial`, so
`Maintenance.Status`) needs a fraction of the endpoints token at a non-empty list (no concurrent
`SetEndpoints`), and `SetEndpoints`/`Sync` the whole token. `New` gives the token when auto-sync is
off (with auto-sync the client's own goroutine changes the endpoints: the token stays with it, and
`Status` is out of reach). `epsTok_persist` freezes the list; a client frozen at one endpoint
(`clientVia c ep := epsTok c DFrac.discard [ep]`) has every call answered by that member, which the
per-member lease reads use (`ApiLease.lean`).

## Handles (persistent unless said)

* `cfgOk cfg γ who` (def): the configuration `New` takes: its endpoints all serve `γ`
  (`servesAt`), its credentials name the principal `who` (`cfgPrincipal`), its dial options keep the
  client's credentials and call each invoker at most once (`dialOptsOk`), its TLS configuration
  (`Transport.tlsCfgOk`), logger and context are usable, and an auto-sync is on only with
  verification off (`Verify.verifyOff`).
* `cfgPrincipal γ cfg who` (opaque): the client's default principal: the user name with a password
  (and, with a client certificate, a certificate the members do not take as a principal); the
  token's user (`tokenUser`); the TLS certificate's (`tlsPrincipal`, 2e's slot); none otherwise.
* `idUpd γ` (def): the identity update the client's own read-only calls hand over (W0's
  `etcdPeek γ` has the same purpose; `idUpd` is kept for the `COMM True` shape).
* `clientBase c who` (opaque): the context (`ctxOk`, `ctxPrin who _ who`), cancel function and
  logger every client has (`Ctx`, `GetLogger`, `Close`'s cancel); `clientPre c γ who` the client
  under construction (`clientBase`, configuration, credentials, `epMu` with endpoints serving `γ`,
  resolver, `callOpts`); `clientCore c γ who` the built client (`clientPre`, the connection, the
  members' fields). Laws: `clientCore_pre`, `clientPre_base`, `clientRest_core` (W0's
  `clientRest`), `isClient_core`, `clientMut_core`.
* `clientBare c who` (exclusive): a `NewCtxClient`'s client before its fields are set
  (`clientBare_assemble`).
* `authAt v γ who`, `clusterAt`, `maintAt` (W0's slots): bundles (`authAt_methods`, ...), realized
  by the handles; `remote*At` the wire bundles, realized by the retry wrappers.

## Requirement snippets

`examples/specreq/clientv3client/`: `lifecycle.go`, `auth.go`, `cluster.go`, `maint.go`,
`kubernetes.go`, `tls.go`, `inproc.go`. `examples/specreq/clientv3lease/` for the lease API.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Api
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.Api
public import Spec.go_etcd_io.etcd.client.pkg.v3.transport.Api


@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## Pure: the RPCs -/

/-- The token refusals the interceptor answers by refreshing the token and resending
(`shouldRefreshToken`): a request so refused was not applied. Each is a refusal (`EtcdErr.refusal`). -/
def errRetryAuth : EtcdErr → Bool
  | .invalidAuthToken | .authOldRevision | .userEmpty => true
  | _ => false

/-- The gRPC method a non-KV request is sent by (`etcdserverpb`'s `AuthClient`, `ClusterClient`,
`MaintenanceClient`, `LeaseClient` method names). -/
def reqRpc : Req → GoString
  | .leaseGrant .. => go!"LeaseGrant"
  | .leaseRevoke _ => go!"LeaseRevoke"
  | .leaseKeepAlive _ => go!"LeaseKeepAlive"
  | .leaseTimeToLive .. => go!"LeaseTimeToLive"
  | .leaseLeases => go!"LeaseLeases"
  | .authEnable => go!"AuthEnable"
  | .authDisable => go!"AuthDisable"
  | .authStatus => go!"AuthStatus"
  | .authenticate .. => go!"Authenticate"
  | .userAdd .. => go!"UserAdd"
  | .userGet _ => go!"UserGet"
  | .userList => go!"UserList"
  | .userDelete _ => go!"UserDelete"
  | .userChangePassword .. => go!"UserChangePassword"
  | .userGrantRole .. => go!"UserGrantRole"
  | .userRevokeRole .. => go!"UserRevokeRole"
  | .roleAdd _ => go!"RoleAdd"
  | .roleGet _ => go!"RoleGet"
  | .roleList => go!"RoleList"
  | .roleDelete _ => go!"RoleDelete"
  | .roleGrantPermission .. => go!"RoleGrantPermission"
  | .roleRevokePermission .. => go!"RoleRevokePermission"
  | .memberAdd .. => go!"MemberAdd"
  | .memberRemove _ => go!"MemberRemove"
  | .memberUpdate .. => go!"MemberUpdate"
  | .memberPromote _ => go!"MemberPromote"
  | .memberList _ => go!"MemberList"
  | .alarmList => go!"Alarm"
  | .alarmDisarm _ => go!"Alarm"
  | .range _ => go!"Range"
  | .put _ => go!"Put"
  | .deleteRange _ => go!"DeleteRange"
  | .txn _ => go!"Txn"
  | .compact .. => go!"Compact"

/-- **The retry wrappers' policy** (`retry.go`): the RPCs sent with `withRepeatablePolicy()`, which
the interceptor resends after an `Unavailable` error (possibly after an applied attempt). -/
def reqRetryRep : Req → Bool
  | .leaseGrant .. | .leaseRevoke _ | .leaseKeepAlive _ | .leaseTimeToLive .. | .leaseLeases
  | .userGet _ | .userList | .roleGet _ | .roleList | .memberList _ | .alarmList | .alarmDisarm _
  | .range _ => true
  | _ => false

/-- **The retry interceptor's options** (`options`): the policy (`rep`: repeatable) and the retry
limit. -/
structure RetryOptsM where
  rep : Bool
  max : w64

/-- `defaultOptions`: non-repeatable, no retry. -/
def RetryOptsM.default : RetryOptsM := { rep := false, max := W64 0 }

/-- Options applied in order (`reuseOrNewWithCallOptions`). -/
def applyRetry (fs : List (RetryOptsM → RetryOptsM)) (o : RetryOptsM) : RetryOptsM :=
  fs.foldl (fun o f => f o) o

/-- `authpb.Permission_Type`'s values (`PermRead`, `PermWrite`, `PermReadWrite`); another value
is not modelled (`none`). -/
def permTypeM (t : w32) : Option PermType :=
  if t = W32 0 then some .read else if t = W32 1 then some .write
  else if t = W32 2 then some .readwrite else none

/-- `etcdserverpb.AlarmType`'s values `NOSPACE`, `CORRUPT` (`NONE` is not an alarm). -/
def alarmKindM (t : w32) : Option AlarmKind :=
  if t = W32 1 then some .nospace else if t = W32 2 then some .corrupt else none


/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The reply message `p` of a non-KV call answered `b`** (owned; 3h realizes it). -/
opaque replyOwn (p : Loc) (b : RespBody) : IProp GF := iprop(True)

/-- **The request message `p` of a non-KV call, modelled by `rq`** (fraction `dq`; 3h). -/
opaque reqOwn (p : Loc) (dq : DFrac) (rq : Req) : IProp GF := iprop(True)

/-- **The TLS configuration at `tls` makes the cluster see the principal `who`** for a request
with no token (persistent; slot, 2e: the certificate's common name if the members run with
`--client-cert-auth`, else none). -/
opaque tlsPrincipal (γ : Cluster) (tls : Loc) (who : Principal) : IProp GF := iprop(True)

/-- **A slice of `grpc.DialOption`s that keep the client's calls sound** (persistent; slot, 2a):
keepalive parameters, context dialers, stats handlers, `WithBlock`, chained interceptors, and
`WithUnaryInterceptor`/`WithStreamInterceptor` (which replace the client's:
`nonissues/etcd-client-dialoptions-unary-interceptor.md`; the gRPC proxy's), each interceptor
calling its invoker or streamer at most once with a context carrying the call's principal; no
per-RPC credentials. -/
opaque dialOptsOk (sl : GoSlice) : IProp GF := iprop(True)

/-- **The default principal of a client configured by `cfg`** (persistent): see the intro laws. -/
opaque cfgPrincipal (γ : Cluster) (cfg : go_etcd_io.etcd.client.v3.Config) (who : Principal) :
  IProp GF := iprop(True)

/-- **The program's permission for the client's own read-only calls**: an atomic update that
changes nothing (see the header). -/
def idUpd (γ : Cluster) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ etcdState γ σ, COMM True }>)

/-- **The configuration `New` takes** for a client of `γ` with default principal `who`. `LogConfig`
(a zap configuration the client would build) is out of scope unless a `Logger` is given. -/
def cfgOk (cfg : go_etcd_io.etcd.client.v3.Config) (γ : Cluster) (who : Principal) : IProp GF :=
  iprop(∃ eps : List GoString, cfg.Endpoints' ↦*□ eps ∗ ([∗list] ep ∈ eps, servesAt γ ep) ∗
    cfgPrincipal γ cfg who ∗ dialOptsOk cfg.DialOptions' ∗
    (⌜cfg.TLS' = null⌝ ∨ Transport.tlsCfgOk cfg.TLS') ∗
    (⌜cfg.Logger' = null ∧ cfg.LogConfig' = null⌝ ∨ Zap.isLogger cfg.Logger') ∗
    (⌜cfg.Context' = GoInterface.nil⌝ ∨ Context.ctxOk cfg.Context' ∗ ctxPrin who cfg.Context' who) ∗
    (⌜cfg.AutoSyncInterval' = W64 0⌝ ∨ Verify.verifyOff) ∗
    idUpd γ)

/-- **A client's context, cancel function and logger** (persistent). -/
opaque clientBase (c : Loc) (who : Principal) : IProp GF := iprop(True)
/-- **The client under construction** (persistent; see the header). -/
opaque clientPre (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- **What the built client's own functions read** (persistent; see the header). -/
opaque clientCore (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- **The client `c` is ready for calls** (persistent): its `Auth` field is set (or it has no
token refresh). -/
opaque clientReady (c : Loc) : IProp GF := iprop(True)
/-- **The client's endpoints are `eps`** (fraction `dq`; the whole token to change them). -/
opaque epsTok (c : Loc) (dq : DFrac) (eps : List GoString) : IProp GF := iprop(True)
/-- **A client frozen at one endpoint**: every call is answered by the member at `ep`. -/
def clientVia (c : Loc) (ep : GoString) : IProp GF := epsTok c DFrac.discard [ep]
/-- **A `NewCtxClient`'s client before its fields are set** (exclusive). -/
opaque clientBare (c : Loc) (who : Principal) : IProp GF := iprop(True)
/-- **A `clientv3.Option` closure** (persistent): `WithZapLogger(lg)`'s (stores a logger). -/
opaque clientOptAt (f : GoFunc) : IProp GF := iprop(True)

/-- **The token bundle `b` holds `""` or tokens of `who`** (`credentials`' bundle). -/
opaque bundleAt (b : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **A retry option `v`** (`retryOption`, persistent): applying it changes the interceptor's
options as `f` does (`withRepeatablePolicy`, `withMax`, `withBackoff`; the backoff function is not
modelled: every one the package makes returns a duration and never panics). -/
opaque retryOptAt (v : go_etcd_io.etcd.client.v3.retryOption) (f : RetryOptsM → RetryOptsM) :
  IProp GF := iprop(True)
def repOptAt (v : go_etcd_io.etcd.client.v3.retryOption) : IProp GF :=
  retryOptAt v (fun o => { o with rep := true })
def maxOptAt (v : go_etcd_io.etcd.client.v3.retryOption) (n : w64) : IProp GF :=
  retryOptAt v (fun o => { o with max := n })
def backoffOptAt (v : go_etcd_io.etcd.client.v3.retryOption) : IProp GF := retryOptAt v id

/-- A read-only slice of retry options acting as `fs`, in order. -/
def retryOptsAt (sl : GoSlice) (fs : List (RetryOptsM → RetryOptsM)) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.retryOption, sl ↦*□ vs ∗
    [∗list] v; f ∈ vs; fs, retryOptAt v f)

/-- **The interceptor's `*options` at `p`** (read-only), modelled by `o`. -/
opaque optionsAt (p : Loc) (o : RetryOptsM) : IProp GF := iprop(True)

/-- **Dial options naming the target** (persistent; slot, 2a and `internal/resolver`):
`grpc.WithResolvers(r)` of an `EtcdManualResolver` whose endpoints all serve `γ`. -/
opaque dialTargetOk (sl : GoSlice) (γ : Cluster) : IProp GF := iprop(True)

/-- **Transport credentials a dial may use** (persistent; slot, 2a). -/
opaque transportCredsOk (creds : GoInterface) : IProp GF := iprop(True)

/-- **The client's dial options** (persistent): the target's, keepalive parameters, the transport
credentials, the client's unary and stream interceptors (`uiOk`, `siOk`) for `c`. -/
opaque clientDialOpts (sl : GoSlice) (c : Loc) (γ : Cluster) (who : Principal) : IProp GF :=
  iprop(True)

/-- **A `backoffFunc`** (persistent): returns a duration for any attempt, never panics. -/
opaque backoffOk (f : GoFunc) : IProp GF := iprop(True)

/-- What a non-KV call returns for the answer `res`: the reply message, or `nil` and `errVal e`. -/
def ansReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok b => iprop(⌜err = GoInterface.nil⌝ ∗ replyOwn resp b)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)

/-- `Authenticate`'s reply: also the token's user (W0's `tokenUser`). -/
def authReply (γ : Cluster) (name : GoString) (res : Resp) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop(ansReply res resp err ∗
    match res with
    | .ok (.authenticate tok) => tokenUser γ tok name
    | _ => True)

/-! ### The call shapes -/

/-- The update of a call by the principal `p`, persistent if `rep`. -/
def callAU (γ : Cluster) (p : Principal) (rq : Req) (rep : Bool)
    (Q : State → State → Resp → IProp GF) : IProp GF :=
  iprop(□?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step p rq σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>)

/-- **A non-KV call** `e` sending `rq` as the principal `p` for the caller's update (persistent if
`rep`), `P` the caller's resources, `B` given back. -/
def CallTriple (e : Expr) (P B : IProp GF) (γ : Cluster) (p : Principal) (rq : Req) (rep : Bool)
    (reply : Resp → Loc → GoInterface → IProp GF) : Prop :=
  ∀ (Q : State → State → Resp → IProp GF),
  {{ P ∗ callAU γ p rq rep Q }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); B ∗
      ((∃ σ σ' res, Q σ σ' res ∗ reply res resp err) ∨ (⌜resp = null⌝ ∗ indefCall err)) }}

/-- **A non-KV call with a local check** (`ok`: the arguments pass it): if they do not, the call
returns an error before sending anything, the update given back. -/
def CheckedCallTriple (e : Expr) (P B : IProp GF) (γ : Cluster) (p : Principal) (rq : Req)
    (rep : Bool) (ok : Prop) (reply : Resp → Loc → GoInterface → IProp GF) : Prop :=
  ∀ (Q : State → State → Resp → IProp GF),
  {{ P ∗ callAU γ p rq rep Q }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); B ∗
      ((⌜ok⌝ ∗ ∃ σ σ' res, Q σ σ' res ∗ reply res resp err) ∨ (⌜ok⌝ ∗ ⌜resp = null⌝ ∗ indefCall err) ∨
       (⌜¬ ok ∧ resp = null ∧ err ≠ GoInterface.nil⌝ ∗ callAU γ p rq rep Q)) }}

/-- **The wire contract of a non-KV unary RPC**: the method `m (reqRpc rq)` sends the request
message `req` (modelled by `rq`, given back) with a context carrying the principal `p`, the update
persistent if the RPC is repeatable, the options `callOptsOk` (a non-repeatable RPC's not
repeatable). -/
def RemoteCallTriple (m : GoString → val) (P : IProp GF) (γ : Cluster)
    (who : Principal) (rq : Req) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (req : Loc) (dq : DFrac) (opts : GoSlice) (rep : Bool),
  (reqRetryRep rq = false → rep = false) →
  CallTriple (App (App (App (Val (m (reqRpc rq))) (Val #ctx)) (Val #req)) (Val #opts))
    iprop(P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ reqOwn req dq rq ∗ callOptsOk opts rep)
    (reqOwn req dq rq) γ p rq (reqRetryRep rq) (wireReply ansReply)

end res

/-! ## The retry interceptor -/

section intc
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A unary call's arguments** (slot, 2a/3h: what a generated stub hands to `cc.Invoke`). -/
opaque unaryArgs (method : GoString) (req reply : GoInterface) (rq : Req)
  (R : Resp → IProp GF) : IProp GF := iprop(True)

/-- **The gRPC call options grpc's invoker accepts** (persistent; slot, 2a). -/
opaque grpcCallOptsOk (sl : GoSlice) : IProp GF := iprop(True)

/-- **A gRPC client connection** (persistent; slot, 2a): `cc.Target()` and grpc's own use of it
are safe. -/
opaque grpcConnAt (cc : Loc) : IProp GF := iprop(True)

/-- **One attempt** (grpc's `UnaryInvoker` `inv`, with the connection `cc`; 2a): success or a
definite error, the update fired; an error after which the request is known not applied (not sent,
a token or learner refusal), the update given back; or another indefinite error, the update lost. -/
def AttemptTriple (inv : val) (cc : Loc) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (method : GoString) (req reply : GoInterface) (rq : Req)
    (R : Resp → IProp GF) (opts : GoSlice) (rep : Bool) (Q : State → State → Resp → IProp GF),
  {{ P ∗ grpcConnAt cc ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ unaryArgs method req reply rq R ∗
      grpcCallOptsOk opts ∗ callAU γ p rq rep Q }}
    (App (App (App (App (App (App (Val inv) (Val #ctx)) (Val #method)) (Val #req)) (Val #reply))
      (Val #cc)) (Val #opts))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' b, Q σ σ' (.ok b) ∗ R (.ok b)) ∨
      (∃ σ σ' e, Q σ σ' (.err e) ∗ callErr err (.etcd e) ∗
        ⌜e.indefinite = false ∧ errRetryAuth e = false ∧ e ≠ .notSupportedForLearner⌝ ∗
        unaryArgs method req reply rq R) ∨
      ((callErr err .notSent ∨
        (∃ e, callErr err (.etcd e) ∗ ⌜errRetryAuth e = true ∨ e = .notSupportedForLearner⌝)) ∗
        callAU γ p rq rep Q ∗ unaryArgs method req reply rq R) ∨
      ((∃ k, callErr err k ∗ ⌜k.indefinite = true ∧ k ≠ .notSent⌝) ∗ unaryArgs method req reply rq R) }}

/-- **The client's unary interceptor `ui`** (persistent): see `uiOk_call`. -/
opaque uiOk (ui : val) (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The client's stream interceptor `si`** (persistent): see `siOk_call`. -/
opaque siOk (si : val) (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **A call through the unary interceptor** of a ready client, for any invoker meeting
`AttemptTriple`: the update fired with a success or a definite answer, or an indefinite error. -/
def uiOk_call.spec : Prop := ∀ (ui : val) (c : Loc) (γ : Cluster) (who : Principal) (inv : val)
    (cc : Loc) (Pinv : IProp GF), AttemptTriple inv cc Pinv γ who →
  ∀ (ctx : GoInterface) (p : Principal) (method : GoString) (req reply : GoInterface) (rq : Req)
    (R : Resp → IProp GF) (opts : GoSlice) (rep : Bool) (Q : State → State → Resp → IProp GF),
  {{ uiOk (GF := GF) ui c γ who ∗ clientReady c ∗ grpcConnAt cc ∗ □ Pinv ∗ Context.ctxOk ctx ∗
      ctxPrin who ctx p ∗ unaryArgs method req reply rq R ∗ callOptsOk opts rep ∗ callAU γ p rq rep Q }}
    (App (App (App (App (App (App (App (Val ui) (Val #ctx)) (Val #method)) (Val #req)) (Val #reply))
      (Val #cc)) (Val inv)) (Val #opts))
  {{ (err : GoInterface), RET #err;
      (∃ σ σ' res, Q σ σ' res ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ b, ⌜res = .ok b⌝ ∗ R res) ∨
         (∃ e, ⌜res = .err e⌝ ∗ callErr err (.etcd e) ∗ unaryArgs method req reply rq R))) ∨
      (indefCall err ∗ unaryArgs method req reply rq R) }}

/-- **A stream opened through the stream interceptor** of a ready client: the client's token
fetched first (`getToken`: an error then, the streamer not called), then the streamer called once
with the context's values added (`withVersion`) and the gRPC options (the limit `0`: no per-call
option raises it, `callOptsOk`); whatever the streamer's triple gives. -/
def siOk_call.spec : Prop := ∀ (si : val) (c : Loc) (γ : Cluster) (who : Principal)
    (strm : val) (P : IProp GF) (Φ : GoInterface → GoInterface → IProp GF)
    (ctx : GoInterface) (p : Principal) (desc cc : Loc) (method : GoString) (opts : GoSlice)
    (rep : Bool),
  (∀ (ctx' : GoInterface) (opts' : GoSlice),
    {{ P ∗ Context.ctxOk ctx' ∗ ctxPrin who ctx' p ∗ Context.ctxWithValues ctx ctx' ∗
        grpcCallOptsOk opts' }}
      (App (App (App (App (App (Val strm) (Val #ctx')) (Val #desc)) (Val #cc)) (Val #method))
        (Val #opts'))
    {{ (s err : GoInterface), RET (PairV #s #err); Φ s err }}) →
  {{ siOk (GF := GF) si c γ who ∗ clientReady c ∗ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗
      callOptsOk opts rep }}
    (App (App (App (App (App (App (Val si) (Val #ctx)) (Val #desc)) (Val #cc)) (Val #method))
      (Val strm)) (Val #opts))
  {{ (s err : GoInterface), RET (PairV #s #err);
      Φ s err ∨ (⌜s = GoInterface.nil⌝ ∗ P ∗
        (indefCall err ∨ ∃ e, callErr err (.etcd e) ∗ ⌜e.refusal = true⌝)) }}

end intc

/-! ## The auth, cluster and maintenance contracts -/

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `UserAddWithOptions`' options: `nil` (a password required) or a read-only message (slot, 3h). -/
opaque userAddOptsAt (p : Loc) (noPw : Bool) : IProp GF := iprop(True)

/-- **One non-KV method call** `f(ctx, args...)` of a client of default principal `who`, with a
context carrying `p`, sending `rq` (the update persistent iff the RPC is repeatable). -/
def Call.Triple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (args : List val) (rq : Req)
    (reply : Resp → Loc → GoInterface → IProp GF := ansReply) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal),
  CallTriple ((args.foldl (fun e a => App e (Val a)) (App (Val f) (Val #ctx))))
    iprop(P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p) iprop(True) γ p rq (reqRetryRep rq) reply

/-- **The `Auth` interface's triples**, one per method (`m s`: the receiver's method `s`). -/
def Auth.methods (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  (∀ name pw : GoString, Call.Triple (m go!"Authenticate") P γ who [ #name, #pw] (.authenticate name pw)
      (authReply γ name)) ∧
  Call.Triple (m go!"AuthEnable") P γ who [] .authEnable ∧
  Call.Triple (m go!"AuthDisable") P γ who [] .authDisable ∧
  Call.Triple (m go!"AuthStatus") P γ who [] .authStatus ∧
  (∀ name pw : GoString, Call.Triple (m go!"UserAdd") P γ who [ #name, #pw] (.userAdd name pw false)) ∧
  (∀ (name pw : GoString) (o : Loc) (noPw : Bool),
    Call.Triple (m go!"UserAddWithOptions") iprop(P ∗ userAddOptsAt o noPw) γ who [ #name, #pw, #o]
      (.userAdd name pw noPw)) ∧
  (∀ name : GoString, Call.Triple (m go!"UserDelete") P γ who [ #name] (.userDelete name)) ∧
  (∀ name pw : GoString, Call.Triple (m go!"UserChangePassword") P γ who [ #name, #pw]
      (.userChangePassword name pw)) ∧
  (∀ user role : GoString, Call.Triple (m go!"UserGrantRole") P γ who [ #user, #role]
      (.userGrantRole user role)) ∧
  (∀ name : GoString, Call.Triple (m go!"UserGet") P γ who [ #name] (.userGet name)) ∧
  Call.Triple (m go!"UserList") P γ who [] .userList ∧
  (∀ name role : GoString, Call.Triple (m go!"UserRevokeRole") P γ who [ #name, #role]
      (.userRevokeRole name role)) ∧
  (∀ name : GoString, Call.Triple (m go!"RoleAdd") P γ who [ #name] (.roleAdd name)) ∧
  (∀ (name key rangeEnd : GoString) (t : w32) (pt : PermType), permTypeM t = some pt →
    Call.Triple (m go!"RoleGrantPermission") P γ who [ #name, #key, #rangeEnd, #t]
      (.roleGrantPermission name { permType := pt, range := { key := key, rangeEnd := rangeEnd } })) ∧
  (∀ name : GoString, Call.Triple (m go!"RoleGet") P γ who [ #name] (.roleGet name)) ∧
  Call.Triple (m go!"RoleList") P γ who [] .roleList ∧
  (∀ role key rangeEnd : GoString, Call.Triple (m go!"RoleRevokePermission") P γ who
      [ #role, #key, #rangeEnd] (.roleRevokePermission role key rangeEnd)) ∧
  (∀ name : GoString, Call.Triple (m go!"RoleDelete") P γ who [ #name] (.roleDelete name))

/-- `MemberAdd`/`MemberAddAsLearner` (the URLs checked first: `Types.urlsValid`). -/
def Cluster.MemberAddTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal)
    (learner : Bool) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (sl : GoSlice) (urls : List GoString),
  CheckedCallTriple (App (App (Val (m (if learner then go!"MemberAddAsLearner" else go!"MemberAdd")))
      (Val #ctx)) (Val #sl))
    iprop(P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ sl ↦*□ urls) iprop(True) γ p
    (.memberAdd urls learner) false (Types.urlsValid urls) ansReply

/-- `MemberUpdate`. -/
def Cluster.MemberUpdateTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) :
    Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (id : w64) (sl : GoSlice) (urls : List GoString),
  CheckedCallTriple (App (App (App (Val (m go!"MemberUpdate")) (Val #ctx)) (Val #id)) (Val #sl))
    iprop(P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ sl ↦*□ urls) iprop(True) γ p
    (.memberUpdate (uint.nat id) urls) false (Types.urlsValid urls) ansReply

/-- `MemberList(ctx, opts...)`: linearizable unless `WithSerializable`. -/
def Cluster.MemberListTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) :
    Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (opts : GoSlice) (gs : List (OpM → OpM)),
  ¬ prefixAndFromKey gs →
  CallTriple (App (App (Val (m go!"MemberList")) (Val #ctx)) (Val #opts))
    iprop(P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ optsAt opts gs) (optsAt opts gs) γ p
    (.memberList (!(opGetM [] gs).serializable)) true ansReply

/-- **The `Cluster` interface's triples.** -/
def Cluster.methods (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  Cluster.MemberAddTriple m P γ who false ∧ Cluster.MemberAddTriple m P γ who true ∧
  (∀ id : w64, Call.Triple (m go!"MemberRemove") P γ who [ #id] (.memberRemove (uint.nat id))) ∧
  Cluster.MemberUpdateTriple m P γ who ∧ Cluster.MemberListTriple m P γ who ∧
  (∀ id : w64, Call.Triple (m go!"MemberPromote") P γ who [ #id] (.memberPromote (uint.nat id)))

/-- **A member's status reply** (`StatusResponse`, owned; member-local: no model; slot, 3h). -/
opaque statusRespOwn (p : Loc) : IProp GF := iprop(True)

/-- **The `Maintenance` value `v` dials through the client `c`** (persistent; `null`: over a
caller's remote, no dial). -/
opaque maintOf (v : GoInterface) (c : Loc) : IProp GF := iprop(True)

/-- `AlarmDisarm` of one model alarm (`alarmKindM`). -/
def Maint.AlarmDisarmTriple (m : GoString → val) (P : IProp GF) (γ : Cluster) (who : Principal) :
    Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (am : Loc) (mid : w64) (t : w32) (k : AlarmKind),
  alarmKindM t = some k →
  CallTriple (App (App (Val (m go!"AlarmDisarm")) (Val #ctx)) (Val #am))
    iprop(P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗
      am.[go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember, go!"MemberID"] ↦□ mid ∗
      am.[go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember, go!"Alarm"] ↦□ t)
    iprop(True) γ p (.alarmDisarm { memberId := uint.nat mid, kind := k }) true ansReply

/-- `Status(ctx, ep)` of a maintenance value dialing through `c`: a fraction of `c`'s endpoints
token at a non-empty list (`Client.dial` reads `c.endpoints[0]` unlocked); member-local reply. -/
def Maint.StatusTriple (m : GoString → val) (v : GoInterface) (P : IProp GF) (γ : Cluster)
    (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (p : Principal) (ep : GoString) (c : Loc) (dq : DFrac) (eps : List GoString),
  {{ P ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ maintOf v c ∗
      (⌜c = null⌝ ∨ epsTok c dq eps ∗ ⌜eps ≠ []⌝) ∗ servesAt γ ep }}
    (App (App (Val (m go!"Status")) (Val #ctx)) (Val #ep))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜c = null⌝ ∨ epsTok c dq eps) ∗
      ((⌜err = GoInterface.nil⌝ ∗ statusRespOwn resp) ∨ ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

/-- **The `Maintenance` interface's triples** (those specified). -/
def Maint.methods (m : GoString → val) (v : GoInterface) (P : IProp GF) (γ : Cluster)
    (who : Principal) : Prop :=
  Call.Triple (m go!"AlarmList") P γ who [] .alarmList ∧
  Maint.AlarmDisarmTriple m P γ who ∧ Maint.StatusTriple m v P γ who

/-- A `*authClient` over the client `c` (`null`: over a caller's remote), of `γ` as `who`. -/
opaque authHandle (a c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- A `*cluster`. -/
opaque clusterHandle (cl c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- A `*maintenance`. -/
opaque maintHandle (mt c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- **The `AuthClient` value `v` meets the wire contract** for the auth requests. -/
opaque remoteAuthAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque remoteClusterAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque remoteMaintAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- A `*retryAuthClient`, `*retryClusterClient`, `*retryMaintenanceClient` over the connection of
the client `c`. -/
opaque retryAuthHandle (r c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque retryClusterHandle (r c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque retryMaintHandle (r c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- The auth requests (`Model.lean`'s `authStep`). -/
def reqIsAuth : Req → Prop
  | .authEnable | .authDisable | .authStatus | .authenticate .. | .userAdd .. | .userGet _
  | .userList | .userDelete _ | .userChangePassword .. | .userGrantRole .. | .userRevokeRole ..
  | .roleAdd _ | .roleGet _ | .roleList | .roleDelete _ | .roleGrantPermission ..
  | .roleRevokePermission .. => True
  | _ => False

def reqIsCluster : Req → Prop
  | .memberAdd .. | .memberRemove _ | .memberUpdate .. | .memberPromote _ | .memberList _ => True
  | _ => False

def reqIsMaint : Req → Prop
  | .alarmList | .alarmDisarm _ => True
  | _ => False

/-! ## Laws -/

def handles1c_persistent.spec : Prop :=
  (∀ γ cfg who, Persistent (cfgPrincipal (GF := GF) γ cfg who)) ∧
  (∀ γ tls who, Persistent (tlsPrincipal (GF := GF) γ tls who)) ∧
  (∀ sl, Persistent (dialOptsOk (GF := GF) sl)) ∧
  (∀ c who, Persistent (clientBase (GF := GF) c who)) ∧
  (∀ c γ who, Persistent (clientPre (GF := GF) c γ who)) ∧
  (∀ c γ who, Persistent (clientCore (GF := GF) c γ who)) ∧
  (∀ c, Persistent (clientReady (GF := GF) c)) ∧
  (∀ c eps, Persistent (epsTok (GF := GF) c DFrac.discard eps)) ∧
  (∀ f, Persistent (clientOptAt (GF := GF) f)) ∧
  (∀ b γ who, Persistent (bundleAt (GF := GF) b γ who)) ∧
  (∀ ui c γ who, Persistent (uiOk (GF := GF) ui c γ who)) ∧
  (∀ si c γ who, Persistent (siOk (GF := GF) si c γ who)) ∧
  (∀ sl, Persistent (grpcCallOptsOk (GF := GF) sl)) ∧
  (∀ cc, Persistent (grpcConnAt (GF := GF) cc)) ∧
  (∀ p b, Persistent (userAddOptsAt (GF := GF) p b)) ∧
  (∀ v c, Persistent (maintOf (GF := GF) v c)) ∧
  (∀ a c γ who, Persistent (authHandle (GF := GF) a c γ who)) ∧
  (∀ a c γ who, Persistent (clusterHandle (GF := GF) a c γ who)) ∧
  (∀ a c γ who, Persistent (maintHandle (GF := GF) a c γ who)) ∧
  (∀ v γ who, Persistent (remoteAuthAt (GF := GF) v γ who)) ∧
  (∀ v γ who, Persistent (remoteClusterAt (GF := GF) v γ who)) ∧
  (∀ v γ who, Persistent (remoteMaintAt (GF := GF) v γ who)) ∧
  (∀ r c γ who, Persistent (retryAuthHandle (GF := GF) r c γ who)) ∧
  (∀ r c γ who, Persistent (retryClusterHandle (GF := GF) r c γ who)) ∧
  (∀ r c γ who, Persistent (retryMaintHandle (GF := GF) r c γ who)) ∧
  (∀ v f, Persistent (retryOptAt (GF := GF) v f)) ∧ (∀ p o, Persistent (optionsAt (GF := GF) p o)) ∧
  (∀ sl γ, Persistent (dialTargetOk (GF := GF) sl γ)) ∧
  (∀ cr, Persistent (transportCredsOk (GF := GF) cr)) ∧
  (∀ sl c γ who, Persistent (clientDialOpts (GF := GF) sl c γ who)) ∧
  (∀ f, Persistent (backoffOk (GF := GF) f))

/-- A user name with a password (and no token) names that user, unless a client certificate the
members take as a principal is configured (then, while auth is off at `New`, the client sends no
token and the members take the certificate's principal once auth is on). -/
def cfgPrincipal_user.spec : Prop := ∀ (γ : Cluster) (cfg : go_etcd_io.etcd.client.v3.Config),
  cfg.Username' ≠ [] → cfg.Password' ≠ [] → cfg.Token' = [] →
  (⌜cfg.TLS' = null⌝ ∨ tlsPrincipal (GF := GF) γ cfg.TLS' none) ⊢
    cfgPrincipal γ cfg (some cfg.Username')

/-- A token (and no user name or password) names the token's user. -/
def cfgPrincipal_token.spec : Prop := ∀ (γ : Cluster) (cfg : go_etcd_io.etcd.client.v3.Config)
    (u : GoString),
  cfg.Token' ≠ [] → cfg.Username' = [] → cfg.Password' = [] →
  tokenUser (GF := GF) γ cfg.Token' u ⊢ cfgPrincipal γ cfg (some u)

/-- No credentials but a TLS configuration: the certificate's principal. -/
def cfgPrincipal_tls.spec : Prop := ∀ (γ : Cluster) (cfg : go_etcd_io.etcd.client.v3.Config)
    (who : Principal),
  (cfg.Username' = [] ∨ cfg.Password' = []) → cfg.Token' = [] →
  tlsPrincipal (GF := GF) γ cfg.TLS' who ⊢ cfgPrincipal γ cfg who

/-- No credentials, no TLS: no principal. -/
def cfgPrincipal_none.spec : Prop := ∀ (γ : Cluster) (cfg : go_etcd_io.etcd.client.v3.Config),
  (cfg.Username' = [] ∨ cfg.Password' = []) → cfg.Token' = [] → cfg.TLS' = null →
  ⊢ cfgPrincipal (GF := GF) γ cfg none

/-- No dial options. -/
def dialOptsOk_nil.spec : Prop := ⊢ dialOptsOk (GF := GF) slice.nil

/-- `Authenticate`'s reply: the token. -/
def replyOwn_authenticate.spec : Prop := ∀ (p : Loc) (tok : GoString),
  replyOwn (GF := GF) p (.authenticate tok) ⊢
    p.[go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse, go!"Token"] ↦ tok ∗
    (p.[go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse, go!"Token"] ↦ tok -∗
      replyOwn p (.authenticate tok))

/-- **`callOptsOk`'s introductions** (W0's slot, realized here: a read-only slice of the client's
gRPC call options and retry options, full to its capacity when not repeatable): the nil slice. -/
def callOptsOk_nil.spec : Prop := ⊢ callOptsOk (GF := GF) slice.nil false

/-- A non-repeatable options slice is full to capacity (`append` allocates). -/
def callOptsOk_full.spec : Prop := ∀ sl, callOptsOk (GF := GF) sl false ⊢ ⌜sl.len = sl.cap⌝

/-- **Appending a retry option**: the repeatable policy makes the slice repeatable; a limit of `0`
or a backoff keeps it (no per-call option raises the limit: no stream is ever wrapped). -/
def callOptsOk_append.spec : Prop := ∀ (sl : GoSlice) (rep : Bool),
  callOptsOk (GF := GF) sl rep ⊢ ∃ os : List GoInterface, sl ↦*□ os ∗
    □ (∀ (sl' : GoSlice) (v : go_etcd_io.etcd.client.v3.retryOption),
        sl' ↦*□ (os ++ [interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #v]) -∗
        ((repOptAt v -∗ callOptsOk sl' true) ∧ (maxOptAt v (W64 0) -∗ callOptsOk sl' rep) ∧
         (backoffOptAt v -∗ callOptsOk sl' rep)))

/-- The pieces of a client. -/
def isClient_core.spec : Prop := ∀ c γ who, isClient (GF := GF) c γ who ⊢ clientCore c γ who
def clientMut_core.spec : Prop := ∀ c γ who, clientMut (GF := GF) c γ who ⊢ clientCore c γ who
/-- W0's `clientRest` (a client whose `KV` field another holds): its own functions' pieces
(`Ctx`, `GetLogger`, `Endpoints`, `Close`). -/
def clientRest_core.spec : Prop := ∀ c γ who, clientRest (GF := GF) c γ who ⊢ clientCore c γ who
def clientCore_pre.spec : Prop := ∀ c γ who, clientCore (GF := GF) c γ who ⊢ clientPre c γ who
def clientPre_base.spec : Prop := ∀ c γ who, clientPre (GF := GF) c γ who ⊢ clientBase c who
def clientConnOk_core.spec : Prop := ∀ c γ who,
  clientCore (GF := GF) c γ who ⊢ clientConnOk c γ who

/-- A built client is ready (`newClient` set `Auth` before returning it). -/
def isClient_ready.spec : Prop := ∀ c γ who, isClient (GF := GF) c γ who ⊢ clientReady c
def clientRest_ready.spec : Prop := ∀ c γ who, clientRest (GF := GF) c γ who ⊢ clientReady c
def clientMut_ready.spec : Prop := ∀ c γ who, clientMut (GF := GF) c γ who ⊢ clientReady c
/-- A handle over a caller's remote needs no client. -/
def clientReady_null.spec : Prop := ⊢ clientReady (GF := GF) null

/-- **The endpoints token**: the list serves the cluster; freezing it (persistent). -/
def epsTok_serves.spec : Prop := ∀ c dq eps γ who,
  clientPre (GF := GF) c γ who ∗ epsTok c dq eps ⊢ [∗list] ep ∈ eps, servesAt γ ep
def epsTok_persist.spec : Prop := ∀ c eps,
  epsTok (GF := GF) c (DFrac.own 1) eps ⊢ |==> epsTok c DFrac.discard eps

/-- **Assembling an in-process client** (`v3client.New`): a `NewCtxClient`'s client whose six
interface fields the caller has set, each meeting its contract for the default principal `none`
(each call's principal is its context's: `ctxPrin none ctx p`, a forwarded token's user). -/
def clientBare_assemble.spec : Prop := ∀ (c : Loc) (γ : Cluster)
    (vk vw vl va vc vm : GoInterface),
  clientBare (GF := GF) c none ∗
    c.[go_etcd_io.etcd.client.v3.Client, go!"KV"] ↦ vk ∗ kvAt vk γ none ∗
    c.[go_etcd_io.etcd.client.v3.Client, go!"Watcher"] ↦ vw ∗ watcherAt vw γ none ∗
    c.[go_etcd_io.etcd.client.v3.Client, go!"Lease"] ↦ vl ∗ leaseAt vl γ none ∗
    c.[go_etcd_io.etcd.client.v3.Client, go!"Auth"] ↦ va ∗ authAt va γ none ∗
    c.[go_etcd_io.etcd.client.v3.Client, go!"Cluster"] ↦ vc ∗ clusterAt vc γ none ∗
    c.[go_etcd_io.etcd.client.v3.Client, go!"Maintenance"] ↦ vm ∗ maintAt vm γ none ∗ maintOf vm null
  ⊢ |==> isClient c γ none ∗ clientReady c

/-- A bare client's context and logger (what the `From*Client` constructors read). -/
def clientBare_base.spec : Prop := ∀ c who,
  clientBare (GF := GF) c who ⊢ clientBase c who ∗ clientBare c who

/-- **The bundles' triples.** -/
def authAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Auth.methods (fun s => v @!! go_etcd_io.etcd.client.v3.Auth.ty @!! s) (authAt (GF := GF) v γ who) γ who
def clusterAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Cluster.methods (fun s => v @!! go_etcd_io.etcd.client.v3.Cluster.ty @!! s)
    (clusterAt (GF := GF) v γ who) γ who
def maintAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Maint.methods (fun s => v @!! go_etcd_io.etcd.client.v3.Maintenance.ty @!! s) v
    (maintAt (GF := GF) v γ who) γ who

/-- **The package's types meet them** once their client is ready (their methods' specs). -/
def authHandle_authAt.spec : Prop := ∀ a c γ who,
  authHandle (GF := GF) a c γ who ∗ clientReady c ⊢
    authAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #a) γ who
def clusterHandle_clusterAt.spec : Prop := ∀ a c γ who,
  clusterHandle (GF := GF) a c γ who ∗ clientReady c ⊢
    clusterAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty) #a) γ who
def maintHandle_maintAt.spec : Prop := ∀ a c γ who,
  maintHandle (GF := GF) a c γ who ∗ clientReady c ⊢
    maintAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty) #a) γ who ∗
    maintOf (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty) #a) c
/-- A client's `Maintenance` field dials through it. -/
def clientCore_maintOf.spec : Prop := ∀ c γ who,
  clientCore (GF := GF) c γ who ⊢
    ∃ v, c.[go_etcd_io.etcd.client.v3.Client, go!"Maintenance"] ↦□ v ∗ maintOf v c

/-- **The wire bundles' triples**: every request of the service, by its method. -/
def remoteAuthAt_call.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal) (rq : Req),
  reqIsAuth rq → RemoteCallTriple (fun s => v @!! go_etcd_io.etcd.api.v3.etcdserverpb.AuthClient.ty @!! s)
    (remoteAuthAt (GF := GF) v γ who) γ who rq
def remoteClusterAt_call.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal) (rq : Req),
  reqIsCluster rq → RemoteCallTriple (fun s => v @!! go_etcd_io.etcd.api.v3.etcdserverpb.ClusterClient.ty @!! s)
    (remoteClusterAt (GF := GF) v γ who) γ who rq
def remoteMaintAt_call.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal) (rq : Req),
  reqIsMaint rq → RemoteCallTriple (fun s => v @!! go_etcd_io.etcd.api.v3.etcdserverpb.MaintenanceClient.ty @!! s)
    (remoteMaintAt (GF := GF) v γ who) γ who rq

/-- The retry wrappers meet the wire contracts once their client is ready. -/
def retryAuthHandle_remoteAuthAt.spec : Prop := ∀ r c γ who,
  retryAuthHandle (GF := GF) r c γ who ∗ clientReady c ⊢
    remoteAuthAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty) #r)
      γ who
def retryClusterHandle_remoteClusterAt.spec : Prop := ∀ r c γ who,
  retryClusterHandle (GF := GF) r c γ who ∗ clientReady c ⊢
    remoteClusterAt
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryClusterClient.ty) #r) γ who
def retryMaintHandle_remoteMaintAt.spec : Prop := ∀ r c γ who,
  retryMaintHandle (GF := GF) r c γ who ∗ clientReady c ⊢
    remoteMaintAt
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryMaintenanceClient.ty) #r)
      γ who

end contracts

end ClientV3
end EtcdGrove
end Perennial
