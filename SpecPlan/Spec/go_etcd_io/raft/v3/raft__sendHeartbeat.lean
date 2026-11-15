/-
## `raft.sendHeartbeat(to, ctx)` (internal)

**Users.** `bcastHeartbeatWithCtx` (`raft.go:733`). **Proof sketch.** The commit sent is at most the
peer's match (R4's `Match`) and the leader's commit, so within the peer's log and committed (the
heartbeat's `msgJust`); the context is the read-only queue's (registered reads only); `send`;
R4's `SentCommit`. **Changes** (from `specs-ref`'s `raft__sendHeartbeat.lean`): over the opened
struct. **Margin.** None on the view.
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

/-- (internal) A leader sends a heartbeat with the read-only queue's context to peer `to`. -/
def raft.sendHeartbeat.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (to : w64) (ctx : GoSlice) (c : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ ownSlice ctx c DFrac.discard ∗
      ⌜o.view.role = StateLeader ∧ to ≠ id ∧ (o.view.prs !! to).isSome ∧ c = hbCtxOf o.ro⌝ }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"sendHeartbeat")) (Val #to)) (Val #ctx))
  {{ RET #(); raftOpen r γ id o ∗ coreInv r γ id o }}

end spec
end Raft
end EtcdGrove
end Perennial
