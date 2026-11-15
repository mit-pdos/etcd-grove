/-
`(*raftNode).advanceTicks(ticks)` (`raft.go:444-448`): `tick()` `ticks` times.
**Users**: `EtcdServer.adjustTicks` (2e). **Proof sketch**: `tick.spec` in a loop. **Changes**: over
`isRaftNode`. **Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

def raftNode.advanceTicks.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc) (ticks : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode r γ id n }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"advanceTicks")) (Val #ticks))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
