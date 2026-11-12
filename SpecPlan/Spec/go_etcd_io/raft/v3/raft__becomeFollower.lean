/-
## `raft.becomeFollower(term, lead)` (internal)

**Users.** `raft.Step` (a higher term, `raft.go:1145`, `:1147`), `stepCandidate` (a leader of the term,
`:1703`-`:1709`, or a lost vote, `:1725`), `stepLeader` (`MsgCheckQuorum`, `:1302`), `switchToConfig`
(`stepDownOnRemoval`, `:2004`), `newRaft` (`:487`), `RawNode.Bootstrap` (`bootstrap.go:52`, inside
`rawNodeAt_bootstrap`'s window).

**Proof sketch.** `reset(term)` (`reset.spec`: a new term forgets the vote; counters, transfer, votes,
progress -- R4's, in place -- and the read-only queue reset; the term only grows); the step function,
tick, leader and role of a follower; `traceBecomeFollower`. The invariant at the new state: the new
term is volatile (bounded by the terms the cluster has seen: the caller's message or the node's own
term); the leader, if any, is the term's (`leaderOf`), which a forwarded transfer request relies on.

**Changes** (from `specs-ref`'s `raft__becomeFollower.lean`): over the opened struct (round 1:
`RawNode.Bootstrap` calls it inside a window where the struct is open). **Margin.** Exact on the
view and the log.
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

/-- (internal) Becomes a follower of term `t` (not below the node's) with leader `l` (none, or the term's leader). -/
def raft.becomeFollower.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (t l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ ⌜uint.nat o.view.hs.term ≤ uint.nat t⌝ ∗
      (⌜l = W64 0⌝ ∨ leaderOf γ t l) }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"becomeFollower")) (Val #t)) (Val #l))
  {{ RET #(); ∃ o', raftOpen r γ id o' ∗ coreInv r γ id o' ∗
      ⌜o'.view = { o.view with hs := if t = o.view.hs.term then o.view.hs else ⟨t, W64 0, o.view.hs.commit⟩,
                               lead := l, role := StateFollower } ∧ o'.log = o.log⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
