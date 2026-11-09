/-
## `(*EtcdServer).MendPeer(id)` (`server.go:2204-2209`)

**Users.** `cluster3.PeerStep`.

**Proof sketch.** The transport's `Resume` of the peer (2f).

**Changes**: as `CutPeer`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **`MendPeer(id)`**: deliver messages to and from member `id` again. -/
def EtcdServer.MendPeer.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat) (p : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"MendPeer")) (Val #p))
  {{ RET #(); threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
