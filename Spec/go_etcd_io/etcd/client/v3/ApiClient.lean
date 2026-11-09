/-
# etcd's Go client: lifecycle, auth, cluster, maintenance, the interceptors (batch 1c)

The vocabulary batch 1c adds to W0's (`Api.lean`): the contracts behind W0's slots `authAt`,
`clusterAt`, `maintAt` (bundles of their methods' triples, in the KV contract's shape), the
configuration `New` takes (`cfgOk`), the principal a configuration names (`cfgPrincipal`), and the
retry interceptor's contract, which is what makes W0's update shapes sound (`AttemptTriple`,
`uiOk`). The lease contract (`leaseAt`) is in `ApiLease.lean`.

## The shape of every non-KV call (`CallTriple`)

As W0's KV contract: the caller's atomic update over `etcdState γ` for the request `rq`
(`Model.lean`'s `Req`: `.userAdd`, `.memberList`, `.leaseGrant`, ...), fired by `Step who rq`, and
the call returns either the answer's reply (`ansReply`: the reply message for `.ok b`, `errVal e`
for `.err e`) with the caller's `Q`, or an error that settles nothing (`indefCall`). The update is
**persistent** (`□`) exactly when the client's retry wrapper marks the RPC repeatable
(`reqRetryRep`: `retry.go`'s `withRepeatablePolicy()`), whether or not the request writes: the
interceptor then resends it after an `Unavailable` error, which may follow an attempt that was
applied, so the cluster may fire the update more than once (**a lease grant may grant two leases, a
revoke may answer `ErrLeaseNotFound` for a lease this very call revoked**: the program's invariant
sees every firing, the caller gets the last one's `Q`). Every other RPC's update is exclusive.

## The retry interceptor's contract (what W0's at-most-once rests on)

`Client.unaryClientInterceptor` is installed on the client's connection; every unary call (the
generated stubs' `cc.Invoke`) runs it around grpc's own one-attempt invoker. The two contracts:

* `AttemptTriple inv` (**what grpc's invoker gives, 2a**): one attempt of a unary call
  (`unaryArgs`: the method, its request message modelled by `rq`, the reply holder) returns
  (1) success, the update fired; (2) a definite etcd error, the update fired with it; (3) an error
  after which the request is known **not applied**, the update **given back unfired**: not sent
  (`CallErr.notSent`), a token refusal (`errRetryAuth`: `ErrInvalidAuthToken`,
  `ErrAuthOldRevision`, `ErrUserEmpty`), or a learner's refusal (`learnerErr`); or (4) an
  indefinite error, the update possibly fired later (lost to the caller).
* `uiOk ui c γ who` (the interceptor's, proved by `Client.unaryClientInterceptor.spec`): for any
  invoker meeting `AttemptTriple`, the interceptor's call returns (1) or (2), or an indefinite
  error, never (3): it resends only after (3) (or, for a repeatable RPC, after an `Unavailable` or
  a timeout of the attempt, the update being persistent), refreshing the token first after a token
  refusal; when it gives up after (3) with a token refusal it **fires the update itself** with that
  refusal (`Step.refuse`: every `retryAuth` error is a refusal), and when the refresh fails it
  fires it with the refresh's error (`ErrAuthFailed`: W0's model must count it a refusal, see
  `notes/specs-only/batch-1c.md`) or returns an indefinite one.

So a non-repeatable write is applied at most once per call: it is resent only after an attempt
that applied nothing.

## Handles (persistent)

* `cfgOk cfg γ who` (def): the configuration `New` takes: its endpoints all serve `γ`
  (`servesAt`), its credentials name the principal `who` (`cfgPrincipal`), its dial options keep the
  client's interceptors (`dialOptsOk`), its TLS configuration, logger and context are usable, and an
  auto-sync is on only with verification off (`Verify.verifyOff`: `Sync` asserts a non-empty member
  list under `ETCD_VERIFY`).
* `cfgPrincipal γ cfg who` (opaque): the principal the cluster sees for a client so configured:
  the user name with a password; the token's user (`tokenOf`); the TLS certificate's (`tlsPrincipal`,
  2e's slot); none otherwise. Intro laws `cfgPrincipal_user`, `cfgPrincipal_token`,
  `cfgPrincipal_tls`, `cfgPrincipal_none`.
* `idUpd γ` (def): the program's permission for the client's own read-only calls (the token
  refresh's `Authenticate`, the auto-sync's `MemberList`): a persistent atomic update that changes
  nothing. The client needs it because those calls are its own, not a caller's: they need an update
  to hand to the cluster, and a read's step changes nothing, so the program loses nothing by giving
  it (its invariant is kept trivially).
* `clientCore c γ who` (opaque): what the client's own functions read (the configuration, the
  credentials and token bundle, the `Auth` field, the endpoints under `epMu`, the logger, `idUpd`).
  Intended realization: read-only points-tos of `cfg`, `creds`, `Username`, `Password`, `Token`,
  `authTokenBundle` (`bundleAt`), `callOpts` (`callOptsOk _ false`), `lg` (an atomic pointer to an
  `isLogger`), `ctx`, `cancel`, `resolver`; an invariant over `epMu` holding `endpoints` with
  `servesAt γ` of each; an invariant holding the `Auth` field (`nil` before `NewAuth`, then
  `authAt`); `idUpd γ`.
* `authAt v γ who`, `clusterAt v γ who`, `maintAt v γ who` (W0's slots): the bundles of the methods'
  triples (`authAt_methods`, ...). Realized for the package's own types by `authHandle_authAt`,
  `clusterHandle_clusterAt`, `maintHandle_maintAt`.
* `remoteAuthAt v γ who`, `remoteClusterAt v γ who`, `remoteMaintAt v γ who` (**the gRPC
  boundary**): the `etcdserverpb.*Client` value `v` meets the wire contract `RemoteCallTriple`:
  the same updates over the request message (`reqOwn`, 3h), errors as gRPC returns them. Realized
  for the retry wrappers (`retryAuthHandle_remoteAuthAt`, ...); the stubs over `connOk` are 2a/3h's.

## Values

* `replyOwn p b` (opaque, 3h): the reply message at `p`, owned, carrying the answer `b`; laws for
  the fields clients read (`replyOwn_authenticate`). `reqOwn p dq rq` (opaque, 3h): the request
  message of a non-KV call.
* `tokenOf γ tok u` (persistent, 3d's slot): the token `tok` names the user `u` while valid.
  `Authenticate`'s reply gives it.
* `bundleAt b γ who` (persistent, `credentials`' realization): the token bundle `b` holds only `""`
  or tokens naming `who`.

## Laws

`handles1c_persistent`; the bundles' triples (`authAt_methods`, `clusterAt_methods`,
`maintAt_methods`); the realizations (`authHandle_authAt`, `clusterHandle_clusterAt`,
`maintHandle_maintAt`, `retryAuthHandle_remoteAuthAt`, ...); `remote*At_call`; `isClient_core`,
`clientMut_core`; `uiOk_call`, `siOk_call`; `learnerErr_indef`; `dialOptsOk_nil`;
`cfgPrincipal_*`; `replyOwn_authenticate`; `callOptsOk_nil`, `callOptsOk_core`.

## Requirement snippets

`examples/specreq/clientv3client/`: `lifecycle.go` (`New`, `Close`, `Endpoints`, `Ctx`, a wrapped
`KV`), `auth.go` (the admin's setup, a user's client, the token refresh's at-most-once),
`cluster.go` (`MemberList`, `MemberAdd`'s answer), `maint.go` (`Status`, `AlarmList`).
`examples/specreq/clientv3lease/` for the lease API.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api
public import Spec.go_uber_org.zap.Api
public import Spec.PkgInit.go_etcd_io.etcd.client.pkg.v3.verify

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

/-- **The token `tok` names the user `u`** while the server accepts it (persistent; slot, 3d). -/
opaque tokenOf (γ : Cluster) (tok : GoString) (u : GoString) : IProp GF := iprop(True)

/-- **The TLS configuration at `tls` makes the cluster see the principal `who`** (persistent; slot,
2e: the certificate's common name if the members run with `--client-cert-auth`, else none). -/
opaque tlsPrincipal (γ : Cluster) (tls : Loc) (who : Principal) : IProp GF := iprop(True)

/-- **A `*tls.Config` grpc's `credentials.NewTLS` may clone** (persistent, read-only; slot, 2a). -/
opaque tlsCfgOk (tls : Loc) : IProp GF := iprop(True)

/-- **A slice of `grpc.DialOption`s that keep the client's interceptors and credentials**
(persistent; slot, 2a): keepalive parameters, context dialers, stats handlers, `WithBlock`, chained
interceptors that call the invoker once with their arguments (Kubernetes' metrics and tracing); not
`WithUnaryInterceptor`/`WithStreamInterceptor` (they replace the client's:
`nonissues/etcd-client-dialoptions-unary-interceptor.md`), not per-RPC credentials. -/
opaque dialOptsOk (sl : GoSlice) : IProp GF := iprop(True)

/-- **The principal of a client configured by `cfg`** (persistent): see the intro laws. -/
opaque cfgPrincipal (γ : Cluster) (cfg : go_etcd_io.etcd.client.v3.Config) (who : Principal) :
  IProp GF := iprop(True)

/-- **The program's permission for the client's own read-only calls**: an atomic update that
changes nothing (see the header). -/
def idUpd (γ : Cluster) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
    <{ etcdState γ σ, COMM True }>)

/-- **`Sync`'s assertion is off** (persistent): the environment variable `ETCD_VERIFY` is neither
`all` nor `assert`, and the program never sets it (`verify.EnableVerifications`). An environment
fact the program states at its start. -/
opaque verifyOff : IProp GF := iprop(True)

/-- **The configuration `New` takes** for a client of `γ` as `who`. `LogConfig` (a zap
configuration the client would build) is out of scope unless a `Logger` is given. -/
def cfgOk (cfg : go_etcd_io.etcd.client.v3.Config) (γ : Cluster) (who : Principal) : IProp GF :=
  iprop(∃ eps : List GoString, cfg.Endpoints' ↦*□ eps ∗ ([∗list] ep ∈ eps, servesAt γ ep) ∗
    cfgPrincipal γ cfg who ∗ dialOptsOk cfg.DialOptions' ∗
    (⌜cfg.TLS' = null⌝ ∨ tlsCfgOk cfg.TLS') ∗
    (⌜cfg.Logger' = null ∧ cfg.LogConfig' = null⌝ ∨ Zap.isLogger cfg.Logger') ∗
    (⌜cfg.Context' = GoInterface.nil⌝ ∨ Context.ctxOk cfg.Context') ∗
    (⌜cfg.AutoSyncInterval' = W64 0⌝ ∨ verifyOff) ∗
    idUpd γ)

/-- **What the client's own functions read** (see the header). -/
opaque clientCore (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The token bundle `b` holds `""` or tokens naming `who`** (`credentials`' bundle). -/
opaque bundleAt (b : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **`withRepeatablePolicy()`'s option** (persistent): sets the retry policy to repeatable. -/
opaque repOptAt (v : go_etcd_io.etcd.client.v3.retryOption) : IProp GF := iprop(True)
/-- **`withMax(n)`'s option** (persistent): sets the retry limit to `n`. -/
opaque maxOptAt (v : go_etcd_io.etcd.client.v3.retryOption) (n : w64) : IProp GF := iprop(True)
/-- **`withBackoff(f)`'s option** (persistent): sets the backoff function. -/
opaque backoffOptAt (v : go_etcd_io.etcd.client.v3.retryOption) : IProp GF := iprop(True)

/-- What a non-KV call returns for the answer `res`: the reply message, or `nil` and `errVal e`. -/
def ansReply (res : Resp) (resp : Loc) (err : GoInterface) : IProp GF :=
  match res with
  | .ok b => iprop(⌜err = GoInterface.nil⌝ ∗ replyOwn resp b)
  | .err e => iprop(⌜err = errVal e ∧ resp = null⌝)

/-- `Authenticate`'s reply: also the token's principal. -/
def authReply (γ : Cluster) (name : GoString) (res : Resp) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop(ansReply res resp err ∗
    match res with
    | .ok (.authenticate tok) => tokenOf γ tok name
    | _ => True)

/-! ### The call shapes -/

/-- **A non-KV call** `e` sending `rq` for the caller's update (persistent if `rep`), `P` the
caller's resources, `B` given back. -/
def CallTriple (e : Expr) (P B : IProp GF) (γ : Cluster) (who : Principal) (rq : Req) (rep : Bool)
    (reply : Resp → Loc → GoInterface → IProp GF) : Prop :=
  ∀ (Q : State → State → Resp → IProp GF),
  {{ P ∗ □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step who rq σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); B ∗
      ((∃ σ σ' res, Q σ σ' res ∗ reply res resp err) ∨ (⌜resp = null⌝ ∗ indefCall err)) }}

/-- **A non-KV call with a local check** (`ok`: the arguments pass it): if they do not, the call
returns an error before sending anything, the update given back. -/
def CheckedCallTriple (e : Expr) (P B : IProp GF) (γ : Cluster) (who : Principal) (rq : Req)
    (rep : Bool) (ok : Prop) (reply : Resp → Loc → GoInterface → IProp GF) : Prop :=
  ∀ (Q : State → State → Resp → IProp GF),
  {{ P ∗ □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step who rq σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); B ∗
      ((⌜ok⌝ ∗ ∃ σ σ' res, Q σ σ' res ∗ reply res resp err) ∨ (⌜ok⌝ ∗ ⌜resp = null⌝ ∗ indefCall err) ∨
       (⌜¬ ok ∧ resp = null ∧ err ≠ GoInterface.nil⌝ ∗
        □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step who rq σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>)) }}

/-- **The wire contract of a non-KV unary RPC**: `v`'s method `reqRpc rq` (of the interface type `ty`)
sends the request message `req` (modelled by `rq`, given back), the update persistent if the RPC is
repeatable, the options `callOptsOk` (a non-repeatable RPC's not repeatable). -/
def RemoteCallTriple (m : GoString → val) (P : IProp GF) (γ : Cluster)
    (who : Principal) (rq : Req) : Prop :=
  ∀ (ctx : GoInterface) (req : Loc) (dq : DFrac) (opts : GoSlice) (rep : Bool),
  (reqRetryRep rq = false → rep = false) →
  CallTriple (App (App (App (Val (m (reqRpc rq))) (Val #ctx)) (Val #req)) (Val #opts))
    iprop(P ∗ Context.ctxOk ctx ∗ reqOwn req dq rq ∗ callOptsOk opts rep) (reqOwn req dq rq)
    γ who rq (reqRetryRep rq) (wireReply ansReply)

end res

/-! ## The retry interceptor -/

section intc
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A unary call's arguments** (slot, 2a/3h: what a generated stub hands to `cc.Invoke`): the
method `method` (`"/etcdserverpb.KV/Put"`, ...), the request message `req` (an `any`, read-only,
modelled by `rq`), the reply holder `reply` (an `any`, owned, empty); `R res` what the caller gets
on success (the filled reply and the request back). -/
opaque unaryArgs (method : GoString) (req reply : GoInterface) (rq : Req)
  (R : Resp → IProp GF) : IProp GF := iprop(True)

/-- **The gRPC call options grpc's invoker accepts** (persistent; slot, 2a): the client's
(`callOptsOk`) without its retry options (`filterCallOptions`), and `grpc.Peer(&p)`. -/
opaque grpcCallOptsOk (sl : GoSlice) : IProp GF := iprop(True)

/-- **`err` is the learner's refusal** (`rpctypes.ErrGRPCNotSupportedForLearner`, slot 2a): a
learner member refused the request before processing it. -/
opaque learnerErr (err : GoInterface) : IProp GF := iprop(True)

/-- The update of a call, persistent if `rep`. -/
def callAU (γ : Cluster) (who : Principal) (rq : Req) (rep : Bool)
    (Q : State → State → Resp → IProp GF) : IProp GF :=
  iprop(□?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step who rq σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>)

/-- **One attempt** (grpc's `UnaryInvoker` `inv`, with the connection `cc`; 2a): success or a
definite error, the update fired; an error after which the request is known not applied, the update
given back; or an indefinite error, the update lost. -/
def AttemptTriple (inv : val) (cc : Loc) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  ∀ (ctx : GoInterface) (method : GoString) (req reply : GoInterface) (rq : Req)
    (R : Resp → IProp GF) (opts : GoSlice) (rep : Bool) (Q : State → State → Resp → IProp GF),
  {{ P ∗ Context.ctxOk ctx ∗ unaryArgs method req reply rq R ∗ grpcCallOptsOk opts ∗
      callAU γ who rq rep Q }}
    (App (App (App (App (App (App (Val inv) (Val #ctx)) (Val #method)) (Val #req)) (Val #reply))
      (Val #cc)) (Val #opts))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' b, Q σ σ' (.ok b) ∗ R (.ok b)) ∨
      (∃ σ σ' e, Q σ σ' (.err e) ∗ callErr err (.etcd e) ∗
        ⌜e.indefinite = false ∧ errRetryAuth e = false⌝ ∗ unaryArgs method req reply rq R) ∨
      ((callErr err .notSent ∨ (∃ e, callErr err (.etcd e) ∗ ⌜errRetryAuth e = true⌝) ∨ learnerErr err) ∗
        callAU γ who rq rep Q ∗ unaryArgs method req reply rq R) ∨
      (indefCall err ∗ unaryArgs method req reply rq R) }}

/-- **The client's unary interceptor `ui`** (persistent): see `uiOk_call`. -/
opaque uiOk (ui : val) (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **The client's stream interceptor `si`** (persistent): see `siOk_call`. -/
opaque siOk (si : val) (c : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

/-- **A call through the unary interceptor**, for any invoker meeting `AttemptTriple`: the update
fired with a success or a definite answer, or an indefinite error; never a token refusal or a
not-sent error left unsettled (the interceptor resends or fires the refusal itself). The options
`callOptsOk opts rep`: a non-repeatable call's update may be exclusive. -/
def uiOk_call.spec : Prop := ∀ (ui : val) (c : Loc) (γ : Cluster) (who : Principal) (inv : val)
    (cc : Loc) (Pinv : IProp GF), AttemptTriple inv cc Pinv γ who →
  ∀ (ctx : GoInterface) (method : GoString) (req reply : GoInterface) (rq : Req)
    (R : Resp → IProp GF) (opts : GoSlice) (rep : Bool) (Q : State → State → Resp → IProp GF),
  {{ uiOk (GF := GF) ui c γ who ∗ □ Pinv ∗ Context.ctxOk ctx ∗ unaryArgs method req reply rq R ∗
      callOptsOk opts rep ∗ callAU γ who rq rep Q }}
    (App (App (App (App (App (App (App (Val ui) (Val #ctx)) (Val #method)) (Val #req)) (Val #reply))
      (Val #cc)) (Val inv)) (Val #opts))
  {{ (err : GoInterface), RET #err;
      (∃ σ σ' res, Q σ σ' res ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ b, ⌜res = .ok b⌝ ∗ R res) ∨
         (∃ e, ⌜res = .err e⌝ ∗ callErr err (.etcd e) ∗ unaryArgs method req reply rq R))) ∨
      (indefCall err ∗ unaryArgs method req reply rq R) }}

/-- **A stream opened through the stream interceptor**: the client's token fetched first
(`getToken`: an error then, the streamer not called), then the streamer called once with the
context's values added (`withVersion`) and the gRPC options; whatever the streamer's triple gives. -/
def siOk_call.spec : Prop := ∀ (si : val) (c : Loc) (γ : Cluster) (who : Principal)
    (strm : val) (P : IProp GF) (Φ : GoInterface → GoInterface → IProp GF)
    (ctx : GoInterface) (desc cc : Loc) (method : GoString) (opts : GoSlice),
  (∀ (ctx' : GoInterface) (opts' : GoSlice),
    {{ P ∗ Context.ctxOk ctx' ∗ Context.ctxWithValues ctx ctx' ∗ grpcCallOptsOk opts' }}
      (App (App (App (App (App (Val strm) (Val #ctx')) (Val #desc)) (Val #cc)) (Val #method))
        (Val #opts'))
    {{ (s err : GoInterface), RET (PairV #s #err); Φ s err }}) →
  {{ siOk (GF := GF) si c γ who ∗ P ∗ Context.ctxOk ctx }}
    (App (App (App (App (App (App (Val si) (Val #ctx)) (Val #desc)) (Val #cc)) (Val #method))
      (Val strm)) (Val #opts))
  {{ (s err : GoInterface), RET (PairV #s #err);
      Φ s err ∨ (⌜s = GoInterface.nil⌝ ∗ P ∗
        (indefCall err ∨ ∃ e, callErr err (.etcd e) ∗ ⌜e.refusal = true ∨ e = .authFailed⌝)) }}

end intc

/-! ## The auth, cluster and maintenance contracts -/

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `UserAddWithOptions`' options: `nil` (a password required) or a read-only message (slot, 3h). -/
opaque userAddOptsAt (p : Loc) (noPw : Bool) : IProp GF := iprop(True)

/-- The auth call `m` with arguments `args` (each `ctx` first), sending `rq`. -/
def Auth.Triple (f : val) (P : IProp GF) (γ : Cluster) (who : Principal) (args : List val) (rq : Req)
    (reply : Resp → Loc → GoInterface → IProp GF := ansReply) : Prop :=
  ∀ (ctx : GoInterface),
  CallTriple ((args.foldl (fun e a => App e (Val a)) (App (Val f) (Val #ctx))))
    iprop(P ∗ Context.ctxOk ctx) iprop(True) γ who rq (reqRetryRep rq) reply

/-- **The `Auth` interface's triples**, one per method: the request each sends (`Model.lean`'s
auth steps). `RoleGrantPermission`: a permission type of the model (`permTypeM`). -/
def Auth.methods (v : GoInterface) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  let m := fun (s : GoString) => v @!! go_etcd_io.etcd.client.v3.Auth.ty @!! s
  (∀ name pw : GoString, Auth.Triple (m go!"Authenticate") P γ who [ #name, #pw] (.authenticate name pw)
      (authReply γ name)) ∧
  Auth.Triple (m go!"AuthEnable") P γ who [] .authEnable ∧
  Auth.Triple (m go!"AuthDisable") P γ who [] .authDisable ∧
  Auth.Triple (m go!"AuthStatus") P γ who [] .authStatus ∧
  (∀ name pw : GoString, Auth.Triple (m go!"UserAdd") P γ who [ #name, #pw] (.userAdd name pw false)) ∧
  (∀ (name pw : GoString) (o : Loc) (noPw : Bool),
    Auth.Triple (m go!"UserAddWithOptions") iprop(P ∗ userAddOptsAt o noPw) γ who [ #name, #pw, #o]
      (.userAdd name pw noPw)) ∧
  (∀ name : GoString, Auth.Triple (m go!"UserDelete") P γ who [ #name] (.userDelete name)) ∧
  (∀ name pw : GoString, Auth.Triple (m go!"UserChangePassword") P γ who [ #name, #pw]
      (.userChangePassword name pw)) ∧
  (∀ user role : GoString, Auth.Triple (m go!"UserGrantRole") P γ who [ #user, #role]
      (.userGrantRole user role)) ∧
  (∀ name : GoString, Auth.Triple (m go!"UserGet") P γ who [ #name] (.userGet name)) ∧
  Auth.Triple (m go!"UserList") P γ who [] .userList ∧
  (∀ name role : GoString, Auth.Triple (m go!"UserRevokeRole") P γ who [ #name, #role]
      (.userRevokeRole name role)) ∧
  (∀ name : GoString, Auth.Triple (m go!"RoleAdd") P γ who [ #name] (.roleAdd name)) ∧
  (∀ (name key rangeEnd : GoString) (t : w32) (pt : PermType), permTypeM t = some pt →
    Auth.Triple (m go!"RoleGrantPermission") P γ who [ #name, #key, #rangeEnd, #t]
      (.roleGrantPermission name { permType := pt, range := { key := key, rangeEnd := rangeEnd } })) ∧
  (∀ name : GoString, Auth.Triple (m go!"RoleGet") P γ who [ #name] (.roleGet name)) ∧
  Auth.Triple (m go!"RoleList") P γ who [] .roleList ∧
  (∀ role key rangeEnd : GoString, Auth.Triple (m go!"RoleRevokePermission") P γ who
      [ #role, #key, #rangeEnd] (.roleRevokePermission role key rangeEnd)) ∧
  (∀ name : GoString, Auth.Triple (m go!"RoleDelete") P γ who [ #name] (.roleDelete name))

/-- `types.NewURLs(urls)` accepts the list (slot, `client/pkg/v3/types`: each a URL with a scheme
`http`, `https`, `unix`, `unixs` and a `host:port`, ...; a pure property of the strings). -/
opaque urlsValid (urls : List GoString) : Prop

/-- **The `Cluster` interface's triples.** `MemberAdd`/`MemberUpdate` check the URLs first
(`urlsValid`: else an error, nothing sent); `MemberList`'s options are `OpOption`s of which only
`WithSerializable` matters (a serializable list is answered from a member's view). -/
def Cluster.methods (v : GoInterface) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  let m := fun (s : GoString) => v @!! go_etcd_io.etcd.client.v3.Cluster.ty @!! s
  (∀ (ctx : GoInterface) (sl : GoSlice) (urls : List GoString) (learner : Bool),
    CheckedCallTriple (App (App (Val (m (if learner then go!"MemberAddAsLearner" else go!"MemberAdd")))
        (Val #ctx)) (Val #sl))
      iprop(P ∗ Context.ctxOk ctx ∗ sl ↦*□ urls) iprop(True) γ who (.memberAdd urls learner) false
      (urlsValid urls) ansReply) ∧
  (∀ (ctx : GoInterface) (id : w64),
    CallTriple (App (App (Val (m go!"MemberRemove")) (Val #ctx)) (Val #id))
      iprop(P ∗ Context.ctxOk ctx) iprop(True) γ who (.memberRemove (uint.nat id)) false ansReply) ∧
  (∀ (ctx : GoInterface) (id : w64) (sl : GoSlice) (urls : List GoString),
    CheckedCallTriple (App (App (App (Val (m go!"MemberUpdate")) (Val #ctx)) (Val #id)) (Val #sl))
      iprop(P ∗ Context.ctxOk ctx ∗ sl ↦*□ urls) iprop(True) γ who (.memberUpdate (uint.nat id) urls)
      false (urlsValid urls) ansReply) ∧
  (∀ (ctx : GoInterface) (opts : GoSlice) (gs : List (OpM → OpM)),
    ¬ prefixAndFromKey gs →
    CallTriple (App (App (Val (m go!"MemberList")) (Val #ctx)) (Val #opts))
      iprop(P ∗ Context.ctxOk ctx ∗ optsAt opts gs) (optsAt opts gs) γ who
      (.memberList (!(opGetM [] gs).serializable)) true ansReply) ∧
  (∀ (ctx : GoInterface) (id : w64),
    CallTriple (App (App (Val (m go!"MemberPromote")) (Val #ctx)) (Val #id))
      iprop(P ∗ Context.ctxOk ctx) iprop(True) γ who (.memberPromote (uint.nat id)) false ansReply)

/-- **A member's status reply** (`StatusResponse`, owned; member-local, no model: its fields are
whatever the member reports; slot, 3h). -/
opaque statusRespOwn (p : Loc) : IProp GF := iprop(True)

/-- **The `Maintenance` interface's triples** (those specified: `AlarmList`, `AlarmDisarm` of one
alarm, `Status`). `AlarmDisarm`'s alarm is one of the model's kinds (`alarmKindM`: not `NONE`, which
asks to disarm every alarm one by one, not one request). `Status` dials the endpoint and answers
what that member reports: no step. -/
def Maint.methods (v : GoInterface) (P : IProp GF) (γ : Cluster) (who : Principal) : Prop :=
  let m := fun (s : GoString) => v @!! go_etcd_io.etcd.client.v3.Maintenance.ty @!! s
  (∀ ctx : GoInterface,
    CallTriple (App (App (Val (m go!"AlarmList")) (Val #ctx)) (Val #()))
      iprop(P ∗ Context.ctxOk ctx) iprop(True) γ who .alarmList true ansReply) ∧
  (∀ (ctx : GoInterface) (am : Loc) (mid : w64) (t : w32) (k : AlarmKind), alarmKindM t = some k →
    CallTriple (App (App (Val (m go!"AlarmDisarm")) (Val #ctx)) (Val #am))
      iprop(P ∗ Context.ctxOk ctx ∗
        am.[go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember, go!"MemberID"] ↦□ mid ∗
        am.[go_etcd_io.etcd.api.v3.etcdserverpb.AlarmMember, go!"Alarm"] ↦□ t)
      iprop(True) γ who (.alarmDisarm { memberId := uint.nat mid, kind := k }) true ansReply) ∧
  (∀ (ctx : GoInterface) (ep : GoString),
    {{ P ∗ Context.ctxOk ctx }}
      (App (App (Val (m go!"Status")) (Val #ctx)) (Val #ep))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ statusRespOwn resp) ∨ (⌜resp = null⌝ ∗ ∃ k, callErr err k) ∨
        ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }})

/-- A `*authClient` of `γ` as `who` (its `remote` a `remoteAuthAt` value, its `callOpts` the
client's). -/
opaque authHandle (a : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- A `*cluster`. -/
opaque clusterHandle (cl : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- A `*maintenance`. -/
opaque maintHandle (mt : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- **The `AuthClient` value `v` meets the wire contract** for the auth requests. -/
opaque remoteAuthAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque remoteClusterAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque remoteMaintAt (v : GoInterface) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
/-- A `*retryAuthClient`, `*retryClusterClient`, `*retryMaintenanceClient`. -/
opaque retryAuthHandle (r : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque retryClusterHandle (r : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)
opaque retryMaintHandle (r : Loc) (γ : Cluster) (who : Principal) : IProp GF := iprop(True)

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
  (∀ γ tok u, Persistent (tokenOf (GF := GF) γ tok u)) ∧
  (∀ γ tls who, Persistent (tlsPrincipal (GF := GF) γ tls who)) ∧
  (∀ tls, Persistent (tlsCfgOk (GF := GF) tls)) ∧
  (∀ sl, Persistent (dialOptsOk (GF := GF) sl)) ∧
  Persistent (verifyOff (GF := GF)) ∧
  (∀ c γ who, Persistent (clientCore (GF := GF) c γ who)) ∧
  (∀ b γ who, Persistent (bundleAt (GF := GF) b γ who)) ∧
  (∀ ui c γ who, Persistent (uiOk (GF := GF) ui c γ who)) ∧
  (∀ si c γ who, Persistent (siOk (GF := GF) si c γ who)) ∧
  (∀ sl, Persistent (grpcCallOptsOk (GF := GF) sl)) ∧
  (∀ err, Persistent (learnerErr (GF := GF) err)) ∧
  (∀ p b, Persistent (userAddOptsAt (GF := GF) p b)) ∧
  (∀ a γ who, Persistent (authHandle (GF := GF) a γ who)) ∧
  (∀ a γ who, Persistent (clusterHandle (GF := GF) a γ who)) ∧
  (∀ a γ who, Persistent (maintHandle (GF := GF) a γ who)) ∧
  (∀ v γ who, Persistent (remoteAuthAt (GF := GF) v γ who)) ∧
  (∀ v γ who, Persistent (remoteClusterAt (GF := GF) v γ who)) ∧
  (∀ v γ who, Persistent (remoteMaintAt (GF := GF) v γ who)) ∧
  (∀ r γ who, Persistent (retryAuthHandle (GF := GF) r γ who)) ∧
  (∀ r γ who, Persistent (retryClusterHandle (GF := GF) r γ who)) ∧
  (∀ r γ who, Persistent (retryMaintHandle (GF := GF) r γ who)) ∧
  (∀ v, Persistent (repOptAt (GF := GF) v)) ∧ (∀ v n, Persistent (maxOptAt (GF := GF) v n)) ∧
  (∀ v, Persistent (backoffOptAt (GF := GF) v))

/-- A user name with a password (and no token) names that user. -/
def cfgPrincipal_user.spec : Prop := ∀ (γ : Cluster) (cfg : go_etcd_io.etcd.client.v3.Config),
  cfg.Username' ≠ [] → cfg.Password' ≠ [] → cfg.Token' = [] →
  ⊢ cfgPrincipal (GF := GF) γ cfg (some cfg.Username')

/-- A token (and no user name or password) names the token's user. -/
def cfgPrincipal_token.spec : Prop := ∀ (γ : Cluster) (cfg : go_etcd_io.etcd.client.v3.Config)
    (u : GoString),
  cfg.Token' ≠ [] → cfg.Username' = [] → cfg.Password' = [] →
  tokenOf (GF := GF) γ cfg.Token' u ⊢ cfgPrincipal γ cfg (some u)

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

/-- The learner's refusal settles nothing to the caller (it is no etcd error of the model). -/
def learnerErr_indef.spec : Prop := ∀ err, learnerErr (GF := GF) err ⊢ indefCall err

/-- `Authenticate`'s reply: the token. -/
def replyOwn_authenticate.spec : Prop := ∀ (p : Loc) (tok : GoString),
  replyOwn (GF := GF) p (.authenticate tok) ⊢
    p.[go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse, go!"Token"] ↦ tok ∗
    (p.[go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse, go!"Token"] ↦ tok -∗
      replyOwn p (.authenticate tok))

/-- **`callOptsOk`'s introductions** (W0's slot, realized here: a read-only slice of the client's
gRPC call options and the retry options above, full to its capacity when not repeatable, so that
appending to it allocates and concurrent calls never write a shared array): the nil slice. -/
def callOptsOk_nil.spec : Prop := ⊢ callOptsOk (GF := GF) slice.nil false

/-- A non-repeatable options slice is full to capacity (`append` allocates). -/
def callOptsOk_full.spec : Prop := ∀ sl, callOptsOk (GF := GF) sl false ⊢ ⌜sl.len = sl.cap⌝

/-- **Appending a retry option**: the repeatable policy makes the slice repeatable; a limit or a
backoff keeps it as it was. (`retry.go`'s wrappers, the lessor's `withMax(0)`.) -/
def callOptsOk_append.spec : Prop := ∀ (sl : GoSlice) (rep : Bool),
  callOptsOk (GF := GF) sl rep ⊢ ∃ os : List GoInterface, sl ↦*□ os ∗
    □ (∀ (sl' : GoSlice) (v : go_etcd_io.etcd.client.v3.retryOption),
        sl' ↦*□ (os ++ [interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #v]) -∗
        ((repOptAt v -∗ callOptsOk sl' true) ∧ (∀ n, maxOptAt v n -∗ callOptsOk sl' rep) ∧
         (backoffOptAt v -∗ callOptsOk sl' rep)))

/-- A client's (or one under construction's) own pieces. -/
def isClient_core.spec : Prop := ∀ c γ who, isClient (GF := GF) c γ who ⊢ clientCore c γ who
def clientMut_core.spec : Prop := ∀ c γ who, clientMut (GF := GF) c γ who ⊢ clientCore c γ who
def clientConnOk_core.spec : Prop := ∀ c γ who,
  clientCore (GF := GF) c γ who ⊢ clientConnOk c γ who

/-- **The bundles' triples.** -/
def authAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Auth.methods v (authAt (GF := GF) v γ who) γ who
def clusterAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Cluster.methods v (clusterAt (GF := GF) v γ who) γ who
def maintAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster) (who : Principal),
  Maint.methods v (maintAt (GF := GF) v γ who) γ who

/-- **The package's types meet them** (their methods' specs). -/
def authHandle_authAt.spec : Prop := ∀ a γ who,
  authHandle (GF := GF) a γ who ⊢
    authAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty) #a) γ who
def clusterHandle_clusterAt.spec : Prop := ∀ a γ who,
  clusterHandle (GF := GF) a γ who ⊢
    clusterAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty) #a) γ who
def maintHandle_maintAt.spec : Prop := ∀ a γ who,
  maintHandle (GF := GF) a γ who ⊢
    maintAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty) #a) γ who

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

/-- The retry wrappers meet the wire contracts (their methods' specs, `retry*Client__*.lean`). -/
def retryAuthHandle_remoteAuthAt.spec : Prop := ∀ r γ who,
  retryAuthHandle (GF := GF) r γ who ⊢
    remoteAuthAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty) #r)
      γ who
def retryClusterHandle_remoteClusterAt.spec : Prop := ∀ r γ who,
  retryClusterHandle (GF := GF) r γ who ⊢
    remoteClusterAt
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryClusterClient.ty) #r) γ who
def retryMaintHandle_remoteMaintAt.spec : Prop := ∀ r γ who,
  retryMaintHandle (GF := GF) r γ who ⊢
    remoteMaintAt
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryMaintenanceClient.ty) #r)
      γ who

end contracts

end ClientV3
end EtcdGrove
end Perennial
