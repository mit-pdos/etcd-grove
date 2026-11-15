/-
## `raft.becomeLeader()` (internal)

**Users.** `stepCandidate` (`raft.go:1719`, after `poll` gave `VoteWon`). **Proof sketch.** Not a
follower (`raft.go:953`); `reset(term)`; its own progress exists (the guard of its campaign: it was
in its configuration, and no conf entry was applied since, the candidate's commit not moving) and
becomes `Replicate`, recently active; `pendingConfIndex` at the last index; `appendEntry` of the
empty entry (never refused: the uncommitted size is zero after `reset`). The invariant: the node is
the term's leader (`leaderOf`, from the votes `poll` counted); the term log starts at its log.
**Changes** (from `specs-ref`'s `raft__becomeLeader.lean`): over the opened struct and `leaderOf`.
**Margin.** The appended entry is not stated.
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

/-- (internal) A candidate that won its term becomes its leader. -/
def raft.becomeLeader.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ ⌜o.view.role = StateCandidate ∧ (o.view.prs !! id).isSome⌝ ∗
      leaderOf γ o.view.hs.term id }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"becomeLeader")) (Val #()))
  {{ RET #(); ∃ o', raftOpen r γ id o' ∗ coreInv r γ id o' ∗
      ⌜o'.view.hs.term = o.view.hs.term ∧ o'.view.hs.vote = o.view.hs.vote ∧ o'.view.lead = id ∧
        o'.view.role = StateLeader ∧ o'.view.prs = o.view.prs⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
