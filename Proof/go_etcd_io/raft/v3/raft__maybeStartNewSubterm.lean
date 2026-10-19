/-
`(*raft).maybeStartNewSubterm` on a witness-free configuration (2026-10-19, witness support).

The empty entry is built as `becomeLeader` built it before raft#168 moved the append here:
`&pb.Entry{Data: nil}`, a fresh struct made an owned entry (`entOwn_of_struct`) and frozen
(`entOwn_freeze`), its one-element slice handed to `appendEntry`, whose time receipt is the least
one (`preceipt_zero`). The two `HasWitness` log lines are dead: the epoch is witness-free.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__maybeStartNewSubterm
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ResetReplicationSet
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ChangeReplicationSet
public import Spec.go_etcd_io.raft.v3.tracker.Epoch__HasWitness
public import Proof.go_etcd_io.raft.v3.LemmasSendR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.maybeStartNewSubterm.wp_proof
    (wp_ProgressTracker_ResetReplicationSet :
      tracker.ProgressTracker.ResetReplicationSet.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ChangeReplicationSet :
      tracker.ProgressTracker.ChangeReplicationSet.spec (GF := GF) (hG := hG))
    (wp_Epoch_HasWitness : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG)) :
    raft.maybeStartNewSubterm.spec (GF := GF) (hG := hG) := by
  intro c r id s nt Hnz
  wp_start as Hphys
  cases nt with
  | false =>
    wp_auto
    -- `ChangeReplicationSet`: no excluded voter, `false`, return `false`
    icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    icases ownTrackerC_epoch $$ Htrk with ⟨#Hep, Htrk⟩
    wp_apply wp_ProgressTracker_ChangeReplicationSet $$ [$Htrkf $Hep] as Htrkf
    ihave Hphys := Hback $$ %tv Htrkf Htrk
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Hphys
  | true =>
    wp_auto
    -- `ResetReplicationSet(true)`: a fresh witness-free epoch
    icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    wp_apply wp_ProgressTracker_ResetReplicationSet c _ tv _ $$ [$Htrkf $Htrk]
      as %e ⟨Htrkf, Htrk⟩
    icases ownTrackerC_epoch $$ Htrk with ⟨#Hep, Htrk⟩
    wp_apply wp_Epoch_HasWitness $$ [$Hep]
    ihave Hphys := Hback $$ %_ Htrkf Htrk
    wp_pures; (try wp_auto)
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
    imod (preceipt_zero (GF := GF)) with #Hrc0
    wp_apply wp_raft_appendEntry c r id _ _ [zero_val EntryM] (DFrac.own 1) 0
        (by simp) (Hnz rfl)
        $$ [$Hphys $Hes $Hrc0]
      as %accepted ⟨-, %Hacc, Hes, Hphys⟩
    -- empty payload, so accepted: the `Panic` branch is dead
    have Hacc' : accepted = true := Hacc (by intro e He; simp at He; subst He; rfl)
    subst Hacc'
    simp only [↓reduceIte]
    wp_auto
    wp_apply raft.wp_load_trk_EpochC c r id _ $$ Hphys as %ep' ⟨Hphys, #Hep'⟩
    wp_apply wp_Epoch_HasWitness $$ [$Hep']
    iapply HΦ
    iexact Hphys

end proof

end EtcdGrove
end Perennial
