/-
## `raft.becomeCandidate()` (internal)

**Users.** `campaign` (`raft.go:1057`). **Proof sketch.** Not a leader (Go panics otherwise,
`raft.go:922`); `reset(term + 1)`; the vote for itself; `traceBecomeCandidate`. The invariant: the
term's increase deposits a time receipt from this function's own step (realization item 5: the term
stays under the bound); the guard `hup` checked (`CampaignGuard`), or the node is a pre-candidate
whose pre-vote was won (the guard survives the pre-vote round: its commit does not move without a
leader's message, which makes it a follower). **Changes** (from `specs-ref`'s
`raft__becomeCandidate.lean`): over the opened struct, the guard named. **Margin.** Exact on the
view.
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

/-- (internal) Becomes a candidate at the next term, voting for itself. -/
def raft.becomeCandidate.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗
      ⌜o.view.role ≠ StateLeader ∧ (CampaignGuard id o ∨ o.view.role = StatePreCandidate)⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"becomeCandidate")) (Val #()))
  {{ RET #(); ∃ o', raftOpen r γ id o' ∗ coreInv r γ id o' ∗
      ⌜o'.view = { o.view with hs := ⟨o.view.hs.term + W64 1, id, o.view.hs.commit⟩,
                               lead := W64 0, role := StateCandidate } ∧ o'.log = o.log⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
