/-
## `(*EtcdServer).checkLeaseLeases(ctx, ...)` (internal helper)

Users: `v3_server.go:740`. Mirrors the code: the auth revision read (3d), `IsAuthEnabled`,
`AuthInfoFromCtx` (its spec), `IsAdminPermitted`, the lessor's lease(s) and their keys (3c), `IsRangePermitted`
for each key (3d), the revision compared again; each check at the auth
store's state when it runs. Changes: the old spec (`specs-ref`'s `EtcdServer__checkLeaseLeases.lean`, the
lease-keys plan) restated over `reqPrin` and the error classes. Margin: which keys and which state
the checks ran at is not stated: the callers fire their update at the return, where W0's step allows a
denial at any state (`leaseTimeToLive`, `leaseLeases`; `srvStep`'s keep-alive disjunct).

Changes: verify-round (client-core's request): a permission denial is fired at W0's three-view `deniedSince` (the auth table the member checked, at or after the call's `lo`: `srvReadAt_auth`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

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

/-- `nil`; a refusal (an invalid token, `ErrUserEmpty`, a stale auth revision); or a denial
(`permErr` of `p` or `tls`). -/
def EtcdServer.checkLeaseLeases.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal) (x : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"checkLeaseLeases")) (Val #ctx)) (Val x))
  {{ (err : GoInterface), RET #err; threadTok ∗
      (⌜err = GoInterface.nil⌝ ∨
       (srvUnfired err ∨ ∃ w, ⌜w = p ∨ w = tls⌝ ∗ srvErr err (AuthState.permErr w)) ∗
         srvErrShape err) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
