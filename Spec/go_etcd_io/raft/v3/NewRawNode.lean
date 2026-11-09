/-
## `NewRawNode(config)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. `RestartNode`, `setupNode`.

**Proof sketch.** As `RestartNode.spec`'s, without `newNode` and the goroutine: `newRaft` (R2)
validates, reads `InitialState` (the client's update fires), restores the tracker (`cf σ`, the
configuration at `a`), applies `Applied`; the `RawNode`'s token holds the raft struct (R2, R3, R4's
predicates) and `S σ` goes into the node's invariant at `γ.ns`.

**Changes** (from `specs-ref`'s `NewRawNode.lean`): one spec for a first start (empty storage) and a
restart (was `RNMode`-indexed); over opaque predicates. **Margin.** The error is always `nil`.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

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

/-- **A `RawNode` for node `id`**, from a storage holding `σ` (as `RestartNode`). -/
def NewRawNode.spec : Prop :=

  ∀ (γ : Cluster) (id : w64) (c : Loc) (cv : go_etcd_io.raft.v3.Config)
    (S : StorState → IProp GF) (cf : StorState → ConfState) (σ : StorState) (a : Nat)
    (m : Membership) (Q : Durable → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗
      ⌜ConfigOk cv ∧ cv.ID' = id⌝ ∗
      ⌜uint.nat cv.Applied' = 0 ∨
        (σ.off ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ uint.nat σ.hs.commit)⌝ ∗
      ⌜max σ.off (uint.nat cv.Applied') ≤ a ∧ (cf σ).Is m⌝ ∗
      (⌜σ.snap.isEmpty⌝ ∨ snapValid γ σ.snap) ∗
      (⌜cv.Logger' = interface.nil⌝ ∨ loggerOk cv.Logger') ∗
      isStorage cv.Storage' S cf ∗ S σ ∗ confAt γ a m ∗ nodeVacant γ id ∗
      (AU <{ ∃∃ (D : Durable), raftState γ id D ∗ ⌜StorageHolds D σ⌝ }> @ ⊤ \ ↑γ.ns, ∅
        <{ raftState γ id D, COMM Q D }>) }}
    (App (Val (@! go_etcd_io.raft.v3.NewRawNode)) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      ∃ (D : Durable) (l : List LogEntry) (cv' : go_etcd_io.raft.v3.Config),
      ⌜err = interface.nil⌝ ∗ c ↦ cv' ∗ rawNode rn γ id ∗ nodeRunning rn 1 ∗ committedLb γ l ∗
      ⌜l.length = max σ.off (uint.nat cv.Applied') ∧
        ∀ j e, σ.off ≤ j → l[j]? = some e → σ.ents[j - σ.off]? = some e⌝ ∗
      nodeDriver rn γ (Driver.start l σ.hs D) ∗ nodeConf rn γ ⟨a, m⟩ ∗
      nodeStorage rn γ S ∗ appliedLb rn l.length ∗ storSnapLb rn (uint.nat σ.snap.index) ∗
      Q D }}

end spec
end Raft
end EtcdGrove
end Perennial
