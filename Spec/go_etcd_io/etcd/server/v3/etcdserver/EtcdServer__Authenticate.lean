/-
## `(*EtcdServer).Authenticate(ctx, r)`

**Users.** The gRPC auth handler (`api/v3rpc/auth.go`, `AuthServer.Authenticate` through
`Authenticator`), etcdctl and the client's `Auth` API (1c). Snippet:
`examples/specreq/etcdserverreq/auth.go`.

**Proof sketch.** `s.read.LinearizableReadNotify(ctx)` (a read path error: unsettled); the loop: `AuthStore().CheckPassword(name, pw)` at the auth store's applied state `kp`, at or after the call's `lo` (3d: the checked revision `rv`; `ErrAuthNotEnabled`, `ErrAuthFailed`: returned before proposing, the update fired at the return, which **needs W0's `authenticate` step to admit those answers from an auth table since `lo`**, as its reads' `deniedSince`: requested, `req/go_etcd_io_etcd_api_v3.md`, "from 2c" round 1), `GenTokenPrefix()` (3d), `raftRequest` of an `InternalAuthenticateRequest{Name, SimpleToken}` at 3h's `.authToken name` with the caller's update over `ao = some (.authenticate name pw)` (`irrAsks`: the password is the update's, not the message's): at the entry's commit the cluster's invariant fires it iff the step admits the apply's answer there (the auth state still the checked one, `rv`'s (then the auth state is `kp`'s: every change bumps the revision, and `AuthEnable` needs a disabled state whose disable bumped it; so `pw` is still `name`'s and the step answers `.ok .authenticate`), or the apply's `ErrAuthNotEnabled`/`ErrAuthFailed` (fired: the step's answers there); otherwise the token is issued and the update given back (`irrBackOk`); the invariant needs no `rv`: the update's `pw` decides). The apply assigns the token to the user (3d: `tokenUser γ tok name`, `irrReply`). Then `checkedRevision == AuthStore().Revision()`: equal, return (the update fired: the applied revision then equals `rv`, so the commit's did); else retry, with the update if it was given back, or without it (fired at an earlier attempt: its `Q`, whose answer carries no token, stays the answer of the last attempt's reply). The deferred `r.Password = ""`. 

**Changes.** The old spec (`specs-ref`'s `EtcdServer__Authenticate.lean`, the auth plan's A3: one per mode,
then merged, over the auth component's predicates) restated over W0's `authStep` and the three
outcomes; auth on and off are states of the model. Round 1: a one-shot update (W0 dropped the token from the answer: the reply carries it, with `tokenUser`), fired at the token entry's commit; no read registry.

**Margin.** As `Put`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Authenticate(ctx, r)`**: authenticates user `name` with `pw` (a one-shot update, fired at the token entry's commit, or at the return for a password-check error); the reply carries a token of `name` (`tokenUser`); the request's password cleared. -/
def EtcdServer.Authenticate.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (p tls : Principal) (r : Loc) (name pw : GoString),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Authenticate")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗
        Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ ClientV3.reqOwn r (DFrac.own 1) (.authenticate name pw))
    iprop(srvGate s q ∗ threadTok ∗ ClientV3.reqOwn r (DFrac.own 1) (.authenticate name [])) γ p tls (.authenticate name pw) false (reqReply γ (.authenticate name pw))

end spec
end EtcdServer
end EtcdGrove
end Perennial
