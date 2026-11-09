/-
## `(*EtcdServer).requireAuthInfo(ctx)` (internal helper)

Users: `LeaseGrant`, `LeaseRevoke`, `LeaseTimeToLive` (`v3_server.go:447,477,699`). Mirrors the code:
`authStore.IsAuthEnabled()` (3d), `AuthInfoFromCtx` (its spec), `ErrUserEmpty` for `nil`. Changes:
restated over `reqPrin`. Margin: whether auth was enabled is not stated (racy).
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

/-- `nil`, or a refusal (an invalid token, `ErrUserEmpty`). -/
def EtcdServer.requireAuthInfo.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"requireAuthInfo")) (Val #ctx))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ⌜err = GoInterface.nil ∨ srvErrOf err .invalidAuthToken ∨ srvErrOf err .userEmpty⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
