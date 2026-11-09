/-
## `raft.reset(term)` (internal)

**Users.** `becomeFollower`, `becomeCandidate`, `becomeLeader` (`raft.go:911`, `:926`, `:957`): run
with the invariant open (the role is set after it). **Proof sketch.** Mirrors the code: a new term
forgets the vote; leader none; counters; `resetRandomizedElectionTimeout`; `abortLeaderTransfer`;
R4's `ResetVotes` and `Visit` (each progress reset in place: `Next = lastIndex + 1`, the node's own
`Match = lastIndex`); `pendingConfIndex`, `uncommittedSize` zero; a new read-only queue (R3's
`newReadOnly`). **Changes.** Over the opened struct (was `NState`). **Margin.** The progress
contents are not stated.
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

/-- (internal) Resets the volatile state for term `t` (not below the node's). -/
def raft.reset.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ ⌜uint.nat o.view.hs.term ≤ uint.nat t⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"reset")) (Val #t))
  {{ RET #(); ∃ o', raftOpen r γ id o' ∗
      ⌜o'.view = { o.view with hs := if t = o.view.hs.term then o.view.hs else ⟨t, W64 0, o.view.hs.commit⟩,
                               lead := W64 0 } ∧
        o'.log = o.log ∧ o'.isLearner = o.isLearner ∧ o'.leadTransferee = W64 0 ∧
        o'.pendingConfIndex = W64 0 ∧ o'.electionElapsed = W64 0 ∧ o'.ro.pending = []⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
