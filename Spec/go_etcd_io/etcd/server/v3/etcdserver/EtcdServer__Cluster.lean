/-
## `(*EtcdServer).Cluster()` (`server.go:627`): translated

**Users.** 2a's headers (`Cluster().ID()`), `start`. **Proof sketch.** The read-only field.
**Changes**: from `specs-ref`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The membership view**, as an `api.Cluster`. -/
def EtcdServer.Cluster.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Cluster")) (Val #()))
  {{ (v : GoInterface), RET #v; ∃ (c : Loc) (γc : Membership.CNames) (cid : w64),
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty) #c⌝ ∗
      Membership.isCluster c γc cid (W64 id) }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
