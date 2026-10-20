/-
`(*raft).maybeStartNewSubterm` (2026-10-19, witness support; 2026-10-20 at any configuration).

The empty entry is built as `becomeLeader` built it before raft#168 moved the append here:
`&pb.Entry{Data: nil}`, a fresh struct made an owned entry (`entOwn_of_struct`) and frozen
(`entOwn_freeze`), its one-element slice handed to `appendEntry`, whose time receipt is the least
one (`preceipt_zero`). The `HasWitness` log lines print the replication sets
(`ReplicationSet.String`), read from the installed epoch.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__maybeStartNewSubterm
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ResetReplicationSet
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ChangeReplicationSet
public import Spec.go_etcd_io.raft.v3.tracker.Epoch__HasWitness
public import Spec.go_etcd_io.raft.v3.tracker.ReplicationSet__String
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

set_option hygiene false in
/-- The tail of `maybeStartNewSubterm` after the replication set is settled: the empty entry
appended (`appendEntry`), the `HasWitness` log line, `true`. At `Hphys : ownRaftPhysCV c _ r id s1`
with `Hnz1 : s1.term ≠ W64 0`. -/
local macro "subterm_tail" : tactic => `(tactic| (
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
        (by simp) Hnz1
        $$ [$Hphys $Hes $Hrc0]
      as %accepted ⟨-, %Hacc, Hes, Hphys⟩
    -- empty payload, so accepted: the `Panic` branch is dead
    have Hacc' : accepted = true := Hacc (by intro e He; simp at He; subst He; rfl)
    subst Hacc'
    simp only [↓reduceIte]
    wp_auto
    wp_apply raft.wp_load_trk_EpochC' c r id _ $$ Hphys as %ep' ⟨Hphys, #Hep'⟩
    iunfold ownEpochOk at Hep'
    icases Hep' with ⟨#Hep', -⟩
    wp_apply wp_Epoch_HasWitness _ _ $$ [$Hep']
    wp_if_destruct
    · try wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      try wp_auto
      wp_raft_logC
    all_goals (try wp_auto)))

theorem raft.maybeStartNewSubterm.wp_proof
    (wp_ProgressTracker_ResetReplicationSet :
      tracker.ProgressTracker.ResetReplicationSet.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ChangeReplicationSet :
      tracker.ProgressTracker.ChangeReplicationSet.spec (GF := GF) (hG := hG))
    (wp_Epoch_HasWitness : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG))
    (wp_ReplicationSet_String : tracker.ReplicationSet.String.spec (GF := GF) (hG := hG))
    (wp_raft_appendEntry : raft.appendEntry.spec (GF := GF) (hG := hG)) :
    raft.maybeStartNewSubterm.spec (GF := GF) (hG := hG) := by
  intro c r id s nt Hnz
  wp_start as Hphys
  cases nt with
  | false =>
    wp_auto
    -- `ChangeReplicationSet`
    icases ownRaftPhysC_tracker_ep c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    wp_apply (tracker.ProgressTracker.ChangeReplicationSet.spec_c
      wp_ProgressTracker_ChangeReplicationSet c _ tv _) $$ [$Htrkf $Htrk] as %ch %e ⟨Htrkf, Hres⟩
    cases ch with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hres with ⟨%He, Htrk⟩
      subst He
      ihave Hphys := Hback $$ %tv %s.ep Htrkf Htrk
      wp_auto
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hphys
    | true =>
      simp only [↓reduceIte]
      icases Hres with ⟨%em', %Hchg, Htrk⟩
      ihave Hphys := Hback $$ %_ %em' Htrkf Htrk
      have Hnz1 : ({ s with ep := em' } : NState).term ≠ W64 0 := Hnz (Or.inr Hchg.1)
      wp_auto
      -- the `Infof` of the new replication set
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      sorry
  | true =>
    wp_auto
    -- `ResetReplicationSet(true)`
    icases ownRaftPhysC_tracker_ep c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
    wp_apply (tracker.ProgressTracker.ResetReplicationSet.spec_c
      wp_ProgressTracker_ResetReplicationSet c _ tv _) $$ [$Htrkf $Htrk]
      as %e ⟨Htrkf, Htrk⟩
    ihave Hphys := Hback $$ %_ %(resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0)) Htrkf Htrk
    have Hnz1 : ({ s with ep := resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0) } :
      NState).term ≠ W64 0 := Hnz (Or.inl rfl)
    wp_auto
    sorry

end proof

end EtcdGrove
end Perennial
