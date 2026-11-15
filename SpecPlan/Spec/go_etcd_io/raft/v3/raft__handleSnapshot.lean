/-
## `raft.handleSnapshot(m)` (internal)

**Users.** `stepFollower`, `stepCandidate` (after becoming a follower of the term).

**Proof sketch.** `EnsureSnapshot` (3h), `restore` (its snapshot valid: `msgSent_snap`); an acknowledgement of the last index or of the commit index.

**Changes** (from `specs-ref`'s `raft__handleSnapshot.lean`): over `raftCore` and `msgSent`.

**Margin.** The new view keeps the term, vote, leader and role; its commit index is not stated.
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

/-- (internal) Handles a `MsgSnap` of the follower's term. -/
def raft.handleSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (ml : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ msgPts ml (DFrac.own 1) m ∗ msgSent γ m ∗
      ⌜m.type = MsgSnap ∧ m.to = id ∧ m.term = ρ.hs.term ∧ ρ.role = StateFollower⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"handleSnapshot")) (Val #ml))
  {{ RET #(); ∃ ρ', raftCore r γ id ρ' ∗ ⌜ρ'.hs.term = ρ.hs.term ∧ ρ'.hs.vote = ρ.hs.vote ∧ ρ'.lead = ρ.lead ∧ ρ'.role = ρ.role⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
