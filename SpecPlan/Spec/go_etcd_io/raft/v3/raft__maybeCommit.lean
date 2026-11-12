/-
## `raft.maybeCommit()` (internal)

**Users.** `stepLeader` (acknowledgements), `switchToConfig`. **Proof sketch.** R4's `Committed()`
(the quorum's match index in the configuration in force) and R3's `maybeCommit` at the leader's term
(only an entry of its term commits by counting): the prefix is committed (`committedLb`), the
deposited updates up to it fire (`committedOps` grows by their entries' `opsOf`). `traceCommit`.
**Changes** (from `specs-ref`'s `raft__maybeCommit.lean`): over `raftCore`; round 1: the result
says whether the commit moved. **Margin.** Exact on the view.
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

/-- (internal) A leader advances its commit index to what a quorum acknowledged at its term. -/
def raft.maybeCommit.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ ⌜ρ.role = StateLeader⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"maybeCommit")) (Val #()))
  {{ (b : Bool), RET #b; ∃ ρ', raftCore r γ id ρ' ∗ ⌜ρ'.hs.term = ρ.hs.term ∧ ρ'.hs.vote = ρ.hs.vote ∧ ρ'.lead = ρ.lead ∧ ρ'.role = ρ.role⌝ ∗
      ⌜uint.nat ρ.hs.commit ≤ uint.nat ρ'.hs.commit ∧ ρ'.prs = ρ.prs ∧
        (b = true ↔ uint.nat ρ.hs.commit < uint.nat ρ'.hs.commit)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
