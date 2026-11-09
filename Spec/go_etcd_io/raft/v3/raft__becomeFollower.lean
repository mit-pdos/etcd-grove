/-
## `raft.becomeFollower(term, lead)` (internal)

**Users.** `raft.Step` (a higher term), `stepCandidate` (a leader of the term, or a lost vote),
`stepLeader` (`MsgCheckQuorum`), `switchToConfig` (`stepDownOnRemoval`), `newRaft`.

**Proof sketch.** `reset(term)` (a new term forgets the vote; counters, the transfer, the votes, the
progress -- R4's, in place -- and the read-only queue reset; the term only grows); the step function,
tick, leader and role of a follower. The leader, if any, is the term's (`leaderOf`): what a stamped
transfer request forwarded to it relies on. `traceBecomeFollower`.

**Changes** (from `specs-ref`'s `raft__becomeFollower.lean`): over `raftCore` and `leaderOf` (was
`NState`'s transition). **Margin.** Exact on the view.
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

/-- (internal) Becomes a follower of term `t` (not below the node's) with leader `l` (none, or the term's leader). -/
def raft.becomeFollower.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (t l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ ⌜uint.nat ρ.hs.term ≤ uint.nat t⌝ ∗
      (⌜l = W64 0⌝ ∨ leaderOf γ t l) }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"becomeFollower")) (Val #t)) (Val #l))
  {{ RET #(); raftCore r γ id
      { ρ with hs := if t = ρ.hs.term then ρ.hs else ⟨t, W64 0, ρ.hs.commit⟩,
                lead := l, role := StateFollower } }}

end spec
end Raft
end EtcdGrove
end Perennial
