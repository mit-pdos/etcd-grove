/-
## `(*EtcdServer).Authenticate(ctx, r)`

**Users.** The gRPC auth handler (`api/v3rpc/auth.go`, `AuthServer.Authenticate` through
`Authenticator`), etcdctl and the client's `Auth` API (1c). Snippet:
`examples/specreq/etcdserverreq/auth.go`.

**Proof sketch.** Registers the caller's persistent update in the read registry (as `Range`); `s.read.LinearizableReadNotify(ctx)` (a read path error: unsettled); the loop: `AuthStore().CheckPassword(name, pw)` at the auth store's applied state `kp` (3d: `ErrAuthNotEnabled`, `ErrAuthFailed`: fired there by the ticket, `authStep`'s answers; the checked revision), `GenTokenPrefix()` (3d), `raftRequest` of an `InternalAuthenticateRequest{Name, SimpleToken}` (no password: its apply assigns the token to the user, 3d: `tokenUser γ tok name`; `raftRequest` at `.authToken name`, which fires no update), then `checkedRevision == AuthStore().Revision()`: equal, the auth state did not change between `kp` and now (every change bumps the revision, and `AuthEnable` needs a disabled state, whose disable bumped it), so the ticket at `kp` with `.ok (.authenticate tok)` gives the reply's `Q`; else retry. The deferred `r.Password = ""`. `raftRequest(ctx, &pb.InternalRaftRequest{...: r})` (`raftRequest.spec`
at `.req (.authenticate name pw)`: the apply's auth store answers by W0's `authStep`, the admin check at the
committed state (3d)), then the type assertion to `*pb.AuthenticateResponse`
(`respTy`).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__Authenticate.lean`, the auth plan's A3: one per mode,
then merged, over the auth component's predicates) restated over W0's `authStep` and the three
outcomes; auth on and off are states of the model.

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

/-- **`s.Authenticate(ctx, r)`**: a token for user `name` if `pw` is its password, at a state the member read after the call began; the update persistent (a read: fired by the registry at the state whose check the answer rests on); the request's password cleared. -/
def EtcdServer.Authenticate.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (r : Loc) (name pw : GoString),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Authenticate")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok ∗ ClientV3.reqOwn r (DFrac.own 1) (.authenticate name pw))
    iprop(threadTok ∗ ClientV3.reqOwn r (DFrac.own 1) (.authenticate name [])) γ who (.authenticate name pw) true (reqReply γ (.authenticate name pw))

end spec
end EtcdServer
end EtcdGrove
end Perennial
