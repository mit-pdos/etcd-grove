/-
`(*EtcdServer).isLeader()` (`server.go:1263-1265`): `MemberID() == Lead()`.

**Users**: `applyEntryNormal` (an empty entry: the leader promotes its lessor), `LeaseRenew`.

**Proof sketch**: the read-only `s.memberID` and the atomic `s.lead` (`srvMember`'s realization).

**Changes**: verify round (A7-provability F7, completeness F3): new here (the old tree's
`EtcdServer__isLeader.lean`).

**Margin**: the boolean is not tied to raft's leadership (the `lead` atomic is the ready handler's last store).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **`isLeader()`**: a boolean (any). -/
def EtcdServer.isLeader.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (id : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvMember s γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"isLeader")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
