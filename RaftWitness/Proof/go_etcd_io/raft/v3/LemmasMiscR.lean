/-
Lemmas of the leaf and utility functions of `raft.go`/`util.go`/`node.go` (raft v3.7 retarget,
stage R4 phase 3, group G1).

* `emptyState_hsRO`: `isInitialized`'s `#emptyState` (`Base.lean`, which is below `InvPb` and
  states it unfolded) is `hsRO es ⟨0, 0, 0⟩`.
* `wp_hsOpt_GetTerm`/`_GetVote`/`_GetCommit`: the getters of a `nil`-or-read-only hard state
  (`hsOpt`), from R1's getter specs (one per case of `hsOpt`).
* `msgOwn_zero`: a fresh `&pb.Message{}` is an owned message holding the zero record
  (`responseToReadIndexReq`'s local case).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPbLog
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPbMsg
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `emptyState` holds a read-only hard state at the zero record (`isInitialized`'s
`#emptyState`, folded into `hsRO`). -/
theorem emptyState_hsRO :
    isInitialized (GF := GF) ⊢
      ∃ es : Loc, (globalAddr emptyState ↦□ es : IProp GF) ∗
        hsRO es (HardStateM.mk (W64 0) (W64 0) (W64 0)) := by
  iintro Hi
  unfold isInitialized
  iNamed Hi
  icases emptyState with ⟨%es, #Hg, %Hnn, #HT, #HV, #HC, #Hpb⟩
  iexists es
  iframe Hg
  iunfold hsRO
  iexists null, null, null, []
  isplitr
  · ipureintro; exact Hnn
  iframe HT HV HC
  isplitr
  · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  isplitr
  · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  isplitr
  · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  unfold pbMsg pbN
  iexact Hpb

/-- The getters of a `nil`-or-read-only hard state. -/
theorem wp_hsOpt_GetTerm (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (p : Loc) (hs : HardStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOpt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #hs.Term'; True }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold hsOpt at H
  icases H with (⟨%Hp, %Hh⟩ | #H)
  · subst Hp Hh
    iapply wp_GetTerm.2.1 $$ Hi HΦ
  · iapply wp_GetTerm.1 p hs $$ [$Hi $H] HΦ

theorem wp_hsOpt_GetVote (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (p : Loc) (hs : HardStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOpt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetVote")) (Val #()))
    {{ RET #hs.Vote'; True }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold hsOpt at H
  icases H with (⟨%Hp, %Hh⟩ | #H)
  · subst Hp Hh
    iapply wp_GetVote.2.1 $$ Hi HΦ
  · iapply wp_GetVote.1 p hs $$ [$Hi $H] HΦ

theorem wp_hsOpt_GetCommit (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (p : Loc) (hs : HardStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsOpt p hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
    {{ RET #hs.Commit'; True }} := by
  iintro %Φ ⟨#Hi, #H⟩ HΦ
  iunfold hsOpt at H
  icases H with (⟨%Hp, %Hh⟩ | #H)
  · subst Hp Hh
    iapply wp_GetCommit.2.1 $$ Hi HΦ
  · iapply wp_GetCommit.1 p hs $$ [$Hi $H] HΦ

/-- A fresh `&pb.Message{}`: an owned message holding the zero record, every list empty. -/
theorem msgOwn_zero (l : Loc) (E : CoPset) :
    (l ↦ (zero_val raftpb.Message) : IProp GF) ⊢
      |={E}=> msgOwn l (DFrac.own 1) ⟨zero_val MessageM, [], none, [], []⟩ := by
  iintro Hl
  ihave Hnil : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnil with #Hnil
  ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnilb with #Hnilb
  ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply msgOwn_of_struct l (zero_val raftpb.Message) [] _ E rfl
  iframe Hl
  simp only [snapOpt]
  iframe Hnil Hnilb Hnilr
  repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
  isplitr
  · iapply BigSepL2.bigSepL2_nil.2; itrivial
  ipureintro; rfl

end lemmas

end EtcdGrove
end Perennial
