/-
`(*raft).maybeStartNewSubterm` (2026-10-19, witness support; 2026-10-20 at any configuration).

The empty entry is built as `becomeLeader` built it before raft#168 moved the append here:
`&pb.Entry{Data: nil}`, a fresh struct made an owned entry (`entOwn_of_struct`) and frozen
(`entOwn_freeze`), its one-element slice handed to `appendEntry`, whose time receipt is the least
one (`preceipt_zero`). The `HasWitness` log lines print the replication sets
(`ReplicationSet.String`), read from the installed epoch.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__maybeStartNewSubterm
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__appendEntry
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ResetReplicationSet
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ChangeReplicationSet
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.Epoch__HasWitness
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ReplicationSet__String
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasSendR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `HasWitness`, its answer a variable (for `wp_if_destruct`). -/
private theorem wp_hasWit (H : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG))
    (e : Loc) (em : EpochM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownEpoch e em }}
      (App (Val (e @!! go.GoType.PointerType tracker.Epoch.ty @!! go!"HasWitness")) (Val #()))
    {{ (b : Bool), RET #b; ⌜b = em.hasWit⌝ }} := by
  iintro %Φ ⟨#Hpkg, #He⟩ HΦ
  iapply H e em $$ [] [HΦ]
  · iframe Hpkg He
  inext
  iintro -
  iapply HΦ
  ipureintro; rfl

theorem raft.maybeStartNewSubterm.wp_proof
    (wp_ProgressTracker_ResetReplicationSet :
      tracker.ProgressTracker.ResetReplicationSet.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ChangeReplicationSet :
      tracker.ProgressTracker.ChangeReplicationSet.spec (GF := GF) (hG := hG))
    (wp_Epoch_HasWitness : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG))
    (wp_ReplicationSet_String : tracker.ReplicationSet.String.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG)) :
    raft.maybeStartNewSubterm.spec (GF := GF) (hG := hG) := by
  intro c r id s nt k Hnz
  wp_start as ⟨Hphys, #Hrc⟩
  cases nt
  -- `newTerm = false`: `ChangeReplicationSet`
  wp_auto
  icases ownRaftPhysC_tracker_ep c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply (tracker.ProgressTracker.ChangeReplicationSet.spec_c
    wp_ProgressTracker_ChangeReplicationSet c _ tv _) $$ [$Htrkf $Htrk] as %ch %e ⟨Htrkf, Hres⟩
  cases ch
  · -- nothing to change: `false`
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with ⟨%He, Htrk⟩
    subst He
    ihave Hphys := Hback $$ %tv %s.ep Htrkf Htrk
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Hphys
  -- the next subterm's epoch
  simp only [↓reduceIte]
  icases Hres with ⟨%em', %Hchg, Htrk⟩
  ihave Hphys := Hback $$ %_ %em' Htrkf Htrk
  have Hnz1 : ({ s with ep := em' } : NState).term ≠ W64 0 := Hnz (Or.inr Hchg.1)
  wp_auto
  -- the `Infof` of the new replication set
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  try wp_auto
  wp_apply raft.wp_load_trk_EpochC' c r id _ $$ Hphys as %e2 ⟨Hphys, #He2⟩
  iunfold ownEpochOk at He2
  icases He2 with ⟨#He2, -⟩
  icases ownEpoch_fields _ _ $$ He2 with ⟨-, ⟨%r0, #Hr0, #Hrs0⟩, -⟩
  try wp_auto
  icases ownRaftPhysC_strLen c r id _ $$ Hphys with ⟨%Hsl0, Hphys⟩
  wp_apply wp_ReplicationSet_String _ r0 _ $$ [$Hr0 $Hrs0]
  · ipureintro; exact Hsl0.1
  iintro %str0 -
  try wp_auto
  wp_apply raft.wp_load_trk_EpochC' c r id _ $$ Hphys as %e3 ⟨Hphys, #He3⟩
  iunfold ownEpochOk at He3
  icases He3 with ⟨#He3, -⟩
  icases ownEpoch_fields _ _ $$ He3 with ⟨-, -, ⟨%r1, #Hr1, #Hrs1⟩⟩
  try wp_auto
  icases ownRaftPhysC_strLen c r id _ $$ Hphys with ⟨%Hsl1, Hphys⟩
  wp_apply wp_ReplicationSet_String _ r1 _ $$ [$Hr1 $Hrs1]
  · ipureintro; exact Hsl1.2
  iintro %str1 -
  try wp_auto
  wp_raft_logC
  rotate_left
  -- `newTerm = true`: `ResetReplicationSet(true)`
  wp_auto
  icases ownRaftPhysC_tracker_ep c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply (tracker.ProgressTracker.ResetReplicationSet.spec_c
    wp_ProgressTracker_ResetReplicationSet c _ tv _) $$ [$Htrkf $Htrk]
    as %e ⟨Htrkf, Htrk⟩
  icases ownTrackerC_epochOk c _ _ $$ Htrk with ⟨#He1, Htrk⟩
  ihave Hphys := Hback $$ %_ %(resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0)) Htrkf Htrk
  have Hnz1 : ({ s with ep := resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0) } :
    NState).term ≠ W64 0 := Hnz (Or.inl rfl)
  try wp_auto
  iunfold ownEpochOk at He1
  icases He1 with ⟨#He1, -⟩
  wp_apply wp_hasWit wp_Epoch_HasWitness _ _ $$ [$He1] as %bw1 %Hbw1
  wp_if_destruct
  rotate_left
  -- the `Infof` of the reset replication set
  try wp_auto
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  try wp_auto
  wp_apply raft.wp_load_trk_EpochC' c r id _ $$ Hphys as %e2 ⟨Hphys, #He2⟩
  iunfold ownEpochOk at He2
  icases He2 with ⟨#He2, -⟩
  icases ownEpoch_fields _ _ $$ He2 with ⟨-, ⟨%r0, #Hr0, #Hrs0⟩, -⟩
  try wp_auto
  icases ownRaftPhysC_strLen c r id _ $$ Hphys with ⟨%Hsl0, Hphys⟩
  wp_apply wp_ReplicationSet_String _ r0 _ $$ [$Hr0 $Hrs0]
  · ipureintro; exact Hsl0.1
  iintro %str0 -
  try wp_auto
  wp_apply raft.wp_load_trk_EpochC' c r id _ $$ Hphys as %e3 ⟨Hphys, #He3⟩
  iunfold ownEpochOk at He3
  icases He3 with ⟨#He3, -⟩
  icases ownEpoch_fields _ _ $$ He3 with ⟨-, -, ⟨%r1, #Hr1, #Hrs1⟩⟩
  try wp_auto
  icases ownRaftPhysC_strLen c r id _ $$ Hphys with ⟨%Hsl1, Hphys⟩
  wp_apply wp_ReplicationSet_String _ r1 _ $$ [$Hr1 $Hrs1]
  · ipureintro; exact Hsl1.2
  iintro %str1 -
  try wp_auto
  wp_raft_logC
  all_goals
    try wp_pures
    try wp_auto
    -- `emptyEnt := &pb.Entry{Data: nil}`: a fresh entry, frozen read-only
    ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSlice_persist $$ Hnilb with #Hnilb
    imod entOwn_of_struct «$r0_ptr»
        { state' := zeroValDef, Term' := null, Index' := null, Type' := null, Data' := slice.nil,
          Subterm' := null, unknownFields' := slice.nil, sizeCache' := 0 }
        (zero_val EntryM) ⊤ rfl $$ [«$r0»] with He
    · iframe «$r0» Hnilb
      msg_nulls
    imod entOwn_freeze $$ He with #He
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %es ⟨Hes, -⟩
    ihave Hes : entsPts _ (DFrac.own 1) [zero_val EntryM] $$ [Hes]
    · iunfold entsPts
      iexists [«$r0_ptr»]
      iframe Hes
      iapply BigSepL2.bigSepL2_singleton.2; iexact He
    wp_auto
    wp_apply wp_raft_appendEntry c r id _ _ [zero_val EntryM] (DFrac.own 1) k
        (by simp) Hnz1
        $$ [$Hphys $Hes $Hrc]
      as %accepted ⟨#Hrc1, %Hacc, Hes, Hphys⟩
    -- empty payload, so accepted: the `Panic` branch is dead
    have Hacc' : accepted = true := Hacc (by intro e He; simp at He; subst He; rfl)
    subst Hacc'
    simp only [↓reduceIte]
    wp_auto
    wp_apply raft.wp_load_trk_EpochC' c r id _ $$ Hphys as %e4 ⟨Hphys, #He4⟩
    iunfold ownEpochOk at He4
    icases He4 with ⟨#He4, -⟩
    wp_apply wp_hasWit wp_Epoch_HasWitness _ _ $$ [$He4] as %bw4 %Hbw4
    wp_if_destruct
    rotate_left
    -- the `Infof` of the new subterm
    try wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    try wp_auto
    wp_apply raft.wp_load_trk_EpochC' c r id _ $$ Hphys as %e5 ⟨Hphys, #He5⟩
    iunfold ownEpochOk at He5
    icases He5 with ⟨#He5, -⟩
    icases ownEpoch_fields _ _ $$ He5 with ⟨#Hsub5, -, -⟩
    try wp_auto
    wp_raft_logC
    all_goals
      try wp_auto
      iapply HΦ
      unfold subtermStart
      simp only [Bool.false_eq_true, ↓reduceIte]
      first
        | (isplitr
           · ipureintro; trivial
           iframe Hrc1 Hphys)
        | (iexists em'
           isplitr; · ipureintro; exact Hchg
           iframe Hrc1 Hphys)

end proof

end EtcdGrove
end Perennial
