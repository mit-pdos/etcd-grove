/-
## `(*EtcdServer).waitLeader(ctx)` (internal helper; untranslated, an assumed contract)

Users: `LeaseRenew`, `leaseTimeToLive` (`v3_server.go:542,676`). The code: the cluster's member for
`Leader()` (`membership`), waiting an election timeout while none (`time.After`), `ErrStopped`,
`ErrNoLeader` on the context's end or a leader without peer URLs. Changes: new as a spec. Margin:
the member returned is any member record (its peer URLs are only used to forward).
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

/-- A member record (`*membership.Member`), or an unsettled error. -/
def EtcdServer.waitLeader.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"waitLeader")) (Val #ctx))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err); threadTok ∗
      ⌜(err = GoInterface.nil ∧ m ≠ null) ∨ (m = null ∧ srvIndef err)⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
