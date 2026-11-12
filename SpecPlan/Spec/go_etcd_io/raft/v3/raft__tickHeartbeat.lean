/-
## `raft.tickHeartbeat()`

**Users.** `RawNode.Tick` through `r.tick` at a leader. Snippet: `step.go` (`ReqTick`).

**Proof sketch.** Counters; past the election timeout: `raft.Step` of a local `MsgCheckQuorum` (with `checkQuorum`), abort a stale transfer; at a leader past the heartbeat timeout: `raft.Step` of `MsgBeat`. Safe at any role (the field's value follows the role, but neither
method relies on it).

**Changes** (from `specs-ref`'s `raft__tickHeartbeat.lean`): over `raftCore` (was `NState` with a tick
credit for the term budget: the budget is the cluster's, `ApiCore.lean`).

**Margin.** Says nothing of the new view. Verify-round (A4 P3): takes and gives the struct's idle token `coreIdle` (it may campaign: `hup`'s scan of `(applied, committed]` needs the published floor at most `applied`, `coreIdle_floor`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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
def raft.tickHeartbeat.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ coreIdle r }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"tickHeartbeat")) (Val #()))
  {{ RET #(); ∃ ρ', raftCore r γ id ρ' ∗ coreIdle r }}

end spec
end Raft
end EtcdGrove
end Perennial
