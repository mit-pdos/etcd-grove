/-
## `setupNode(c, peers)` (internal)

**Users.** `StartNode`. **Proof sketch.** `NewRawNode`, `Bootstrap`, `newNode`, allocate it; the
node's invariant is allocated (`isNode`), the loop's part kept for `run` (`nodeLoop`). **Changes.**
`StartNode.spec` without the goroutine.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

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
variable [ctx_sem : context.Assumptions]

/-- (internal) `StartNode` without starting the goroutine: returns `nodeLoop` for it. -/
def setupNode.spec : Prop :=

  ∀ (γ : Cluster) (id : w64) (c : Loc) (cv : go_etcd_io.raft.v3.Config) (peers : GoSlice)
    (dq : DFrac) (ps : List (w64 × List w8)) (boot : List LogEntry)
    (S : StorState → IProp GF) (cf : StorState → ConfState) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗
      ⌜ConfigOk cv ∧ cv.ID' = id ∧ cv.Applied' = W64 0 ∧ ps ≠ [] ∧ BootLog ps boot ∧
        cf StorState.empty = ConfState.empty⌝ ∗
      (⌜cv.Logger' = interface.nil⌝ ∨ loggerOk cv.Logger') ∗
      isStorage cv.Storage' S cf ∗ S StorState.empty ∗ peersPts peers dq ps ∗ bootLog γ boot ∗
      nodeVacant γ id ∗
      (AU <{ ∃∃ (D : Durable), raftState γ id D ∗ ⌜D = Durable.init⌝ }> @ ⊤ \ ↑γ.ns, ∅
        <{ raftState γ id D, COMM Q }>) }}
    (App (App (Val (@! go_etcd_io.raft.v3.setupNode)) (Val #c)) (Val #peers))
  {{ (n : Loc), RET #n;
      ∃ (cv' : go_etcd_io.raft.v3.Config), c ↦ cv' ∗ isNode n γ id ∗ nodeLoop n ∗ nodeRunning n 1 ∗
      nodeDriver n γ (Driver.start [] HardState.empty Durable.init) ∗
      nodeConf n γ ⟨boot.length, Membership.simple (listToSet (ps.map (·.1)))⟩ ∗
      nodeStorage n γ S ∗ appliedLb n 0 ∗ storSnapLb n 0 ∗ peersPts peers dq ps ∗ Q }}

end spec
end Raft
end EtcdGrove
end Perennial
