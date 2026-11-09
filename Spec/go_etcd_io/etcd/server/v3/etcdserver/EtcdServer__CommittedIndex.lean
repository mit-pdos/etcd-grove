/-
`(*EtcdServer).CommittedIndex()` (`server.go:1764`): `s.getCommittedIndex()`.

**Users**: v3rpc's `maintenanceServer.Status` (`maintenance.go:277`), etcd's tests.

**Proof sketch**: the atomic `s.committedIndex` (`srvMember`'s realization: any value).

**Changes**: verify round (A7-completeness F3, A8-completeness F5): new here (the old tree's
`EtcdServer__CommittedIndex.lean`).

**Margin**: the value is not tied to the committed log (a status report).
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

/-- **`CommittedIndex()`**: an index (any). -/
def EtcdServer.CommittedIndex.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"CommittedIndex")) (Val #()))
  {{ (i : w64), RET #i; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
