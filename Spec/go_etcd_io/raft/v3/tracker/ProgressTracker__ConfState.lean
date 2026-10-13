/-
Port of election_proof/spec_ProgressTracker__ConfState.v (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `tv` is written out
(`tracker.ProgressTracker`), as `ownTracker` forces it.
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrackerC
public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `p.ConfState()` is the `ConfState` of the active configuration (tracker.go:
`Voters: p.Voters[0].Slice()`, `VotersOutgoing: p.Voters[1].Slice()`, `Learners:
quorum.MajorityConfig(p.Learners).Slice()`, `LearnersNext: ...`, `AutoLeave: p.AutoLeave`):
each list a permutation of its set (really sorted).

At any configuration since 2026-10-13 (reconfiguration stage A1; `ownTrackerC`): the four sets
of `c` and its `AutoLeave`. The statement at a simple configuration (`ownTracker cfg`: the
voters `cfg`, the learners the tracked ids outside `cfg`, and -- for the empty outgoing
voters and staged learners -- only the lengths, all any caller needs) is
`tracker.ProgressTracker.ConfState.spec_simple`, which `switchToConfig` uses. -/
abbrev tracker.ProgressTracker.ConfState.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"ConfState"))
      (Val #()))
  {{ (cs : raftpb.ConfState) (xs os ls lns : List w64), RET #cs;
      trk ↦ tv ∗ ownTrackerC c tv t ∗
      cs.Voters' ↦* xs ∗ cs.VotersOutgoing' ↦* os ∗ cs.Learners' ↦* ls ∗
      cs.LearnersNext' ↦* lns ∗
      ⌜xs ≡ₚ elements c.incoming ∧ os ≡ₚ elements c.outgoing ∧ ls ≡ₚ elements c.learners ∧
        lns ≡ₚ elements c.learnersNext ∧ cs.AutoLeave' = c.autoLeave⌝ }}

open Iris.ProofMode in
/-- The statement until 2026-10-13, at a simple configuration (`ownTracker`). -/
theorem tracker.ProgressTracker.ConfState.spec_simple
    (H : tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG))
    (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"ConfState"))
      (Val #()))
  {{ (cs : raftpb.ConfState) (xs ls : List w64), RET #cs;
      trk ↦ tv ∗ ownTracker cfg tv t ∗
      cs.Voters' ↦* xs ∗ cs.Learners' ↦* ls ∗
      ⌜xs ≡ₚ elements cfg ∧ ls ≡ₚ elements (domSet t.prs \ cfg) ∧
        cs.VotersOutgoing'.len = W64 0 ∧
        cs.LearnersNext'.len = W64 0 ∧
        cs.AutoLeave' = false⌝ }} := by
  iintro %Φ ⟨#Hpkg, Htrk, Hown⟩ HΦ
  ihave Hown := ownTracker_toC _ _ _ $$ Hown
  iapply H _ trk tv t $$ [$Hpkg $Htrk $Hown]
  inext
  iintro %cs %xs %os %ls %lns ⟨Htrk, Hown, Hxs, Hos, Hls, Hlns, %Hp⟩
  icases ownTrackerC_toTracker _ _ _ _ $$ Hown with ⟨Hown, -⟩
  obtain ⟨H0, H1, H2, H3, H4⟩ := Hp
  obtain rfl := perm_elements_empty os H1
  obtain rfl := perm_elements_empty lns H3
  ihave %Hl1 := ownSlice_len $$ Hos
  ihave %Hl3 := ownSlice_len $$ Hlns
  iapply HΦ
  iframe Htrk Hown Hxs Hls
  ipureintro
  refine ⟨H0, H2, ?_, ?_, H4⟩
  · simp at Hl1; word
  · simp at Hl3; word

end spec

end EtcdGrove
end Perennial
