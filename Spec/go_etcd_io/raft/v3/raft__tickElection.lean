/-
## `raft.tickElection()`

**Users.** `RawNode.Tick` (`rawnode.go:64-66`) through `r.tick` (`raftRO_peek`: the field holds this method value at a follower, candidate or pre-candidate); `node.run`'s `tickc` arm (`node.go:433-434`). Snippet: `step.go` (`ReqTick`).

**Proof sketch.** `electionElapsed++`; promotable and past the randomized timeout: `raft.Step` of a local `MsgHup` (`stepIn`'s report case), whose error is `nil`. Safe at any role (the field's value follows the role, but neither
method relies on it).

**Changes** (from `specs-ref`'s `raft__tickElection.lean`): over `raftCore` (was `NState` with a tick
credit for the term budget: the budget is the cluster's, `ApiCore.lean`).

**Margin.** Says nothing of the new view.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A tick of node `id`'s raft struct. -/
def raft.tickElection.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"tickElection")) (Val #()))
  {{ RET #(); ∃ ρ', raftCore r γ id ρ' }}

end spec
end Raft
end EtcdGrove
end Perennial
