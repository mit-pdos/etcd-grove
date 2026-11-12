/-
`(*raftNode).tick()` (`raft.go:156-161`): under `tickMu`, `r.Tick()` (R1's `node.Tick.spec`) and
record the time.

**Users**: the loop (`raft.go:186`), `advanceTicks` (`adjustTicks`, 2e). Snippet `raftnode.go`
(`ReqDriverLoop`). **Proof sketch**: `tickMu`'s lock invariant over `latestTickTs` (`isRaftNode`).
**Changes**: over `isRaftNode`. **Margin**: none.
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

def raftNode.tick.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode r γ id n }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"tick")) (Val #()))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
