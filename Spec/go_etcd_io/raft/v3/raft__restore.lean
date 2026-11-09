/-
## `raft.restore(s)` (internal)

**Users.** `handleSnapshot`. **Proof sketch.** Not past the commit index: refused. A follower
(the defensive step-down is unreachable). Not in the snapshot's configuration: refused. The
snapshot's last entry matches the log: commit fast-forwarded (`commitTo`: it is committed,
`snapValid_committed`). Else R3's `restore` (the log becomes the snapshot, pending; committed at its
index). The configuration switches only at `appliedSnap` (the fork's fix,
`issues/raft-snapshot-during-apply-stale-confchange.md`).

**Changes** (from `specs-ref`'s `raft__restore.lean`): over `raftCore` and `snapValid` (was
`SnapScope` over `NState`). Round 1: the commit and the result stated. **Margin.** A refusal
does not say which check refused (stale, not in the configuration, or fast-forwarded).
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

/-- (internal) Restores a valid snapshot at a follower, or refuses it. -/
def raft.restore.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (sp : Loc) (s : Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ snapshotPts sp DFrac.discard s ∗ snapValid γ s ∗
      ⌜ρ.role = StateFollower⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"restore")) (Val #sp))
  {{ (b : Bool), RET #b; ∃ ρ', raftCore r γ id ρ' ∗ ⌜ρ'.hs.term = ρ.hs.term ∧ ρ'.hs.vote = ρ.hs.vote ∧ ρ'.lead = ρ.lead ∧ ρ'.role = ρ.role⌝ ∗
      ⌜uint.nat ρ.hs.commit ≤ uint.nat ρ'.hs.commit ∧ (b = true → ρ'.hs.commit = s.index)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
