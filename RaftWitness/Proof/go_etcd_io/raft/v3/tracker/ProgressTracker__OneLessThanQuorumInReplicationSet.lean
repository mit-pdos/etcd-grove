/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/ProgressTracker__OneLessThanQuorumInReplicationSet.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__OneLessThanQuorumInReplicationSet
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.witnessIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.Epoch__ReplicateToWitness
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.matchAckIndexer__AckedIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.scopedAckIndexer__AckedIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__OneLessThanQuorum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The tracker scopes the progress map to each half's regular voters and uses
`witnessIndex` for that half's threshold. A shared witness receives the lower index. -/
theorem tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.wp_proof
    (wp_ReplicateToWitness : tracker.Epoch.ReplicateToWitness.spec (GF := GF) (hG := hG))
    (wp_witnessIndex : tracker.witnessIndex.spec (GF := GF) (hG := hG))
    (wp_matchAckIndexer_AckedIndex :
      tracker.matchAckIndexer.AckedIndex.spec (GF := GF) (hG := hG))
    (wp_scopedAckIndexer_AckedIndex :
      tracker.scopedAckIndexer.AckedIndex.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec (GF := GF) (hG := hG) := by
  intro trk dq tv em V0 V1 pvs
  wp_start as ⟨Htrk, #He, Hres⟩
  wp_auto
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Epoch"] ↦{dq} tv.Epoch')
      (A' := trk.[tracker.ProgressTracker, go!"Epoch"] ↦{dq} tv.Epoch')
      (P := trk ↦{dq} tv)) $$ Htrk with ⟨Hef, Htrkback⟩
  wp_auto
  ihave Htrk := Htrkback $$ Hef
  wp_apply wp_ReplicateToWitness tv.Epoch' em $$ [$He]
  -- no half replicates to its witness: `return nil`
  by_cases Hnone : em.rs0.rep = false ∧ em.rs1.rep = false
  · obtain ⟨h0, h1⟩ := Hnone
    rw [h0, h1]
    wp_auto
    iapply HΦ
    iframe Htrk Hres
    ileft; ipureintro; exact ⟨⟨h0, h1⟩, rfl⟩
  have Hsome : em.rs0.rep = true ∨ em.rs1.rep = true := by
    cases h0 : em.rs0.rep <;> cases h1 : em.rs1.rep <;> simp_all
  icases Hres with (%Hf | Hres)
  · exact absurd Hf Hnone
  iunfold oltqRes at Hres
  icases Hres with ⟨%Hdq, %vin, %vout, %Hvv, Hin, Hout, Hpm⟩
  obtain ⟨Harr, Hsz0, Hsz1⟩ := Hvv
  subst Hdq
  -- the condition `!w1 && !w2` is false, whichever half replicates
  wp_bind (If (Val #(!em.rs0.rep)) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #false⌝ ∗ w2_ptr ↦ em.rs1.rep))) $$ [w2]
  · cases h0 : em.rs0.rep
    · have h1 : em.rs1.rep = true := by simp_all
      wp_auto
      iframe w2
      ipureintro; simp [h1]
    · wp_auto
      iframe w2
      ipureintro; rfl
  iintro %v ⟨%Hv, w2⟩
  subst Hv
  -- the epoch's halves, read-only
  icases ownEpoch_fields tv.Epoch' em $$ He with ⟨-, ⟨%r0, #Hr0, #Hrs0⟩, ⟨%r1, #Hr1, #Hrs1⟩⟩
  icases ownRS_fields _ r0 em.rs0 $$ [Hr0 Hrs0] with ⟨#Hw0, -, #Hn0⟩
  · iframe Hr0 Hrs0
  icases ownRS_fields _ r1 em.rs1 $$ [Hr1 Hrs1] with ⟨#Hw1, -, #Hn1⟩
  · iframe Hr1 Hrs1
  wp_auto
  wp_bind (If (Val #(_ : Bool)) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(sharedWitness em)⌝ ∗ epoch_ptr ↦ tv.Epoch')))
    $$ [epoch]
  · wp_if_destruct <;> (try wp_auto) <;> iframe epoch <;> ipureintro <;>
      simp_all [sharedWitness]
  iintro %v ⟨%Hv, epoch⟩
  subst Hv
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := w64) as %rm Hrm
  -- the progress map as an indexer (`matchAckIndexer`), and each half's scope
  ihave #Hm : isAckedIndexer (interface.mkOk tracker.matchAckIndexer.ty #tv.Progress')
      (ownProgressMap tv.Progress' pvs) (pvsAcked pvs) $$ []
  · iunfold isAckedIndexer
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %id %Ψ
    imodintro
    iintro HP HΨ
    wp_apply wp_matchAckIndexer_AckedIndex $$ [$HP] as HP
    iapply HΨ $$ HP
  ihave #Hrs0' := Hrs0
  iunfold ownRS at Hrs0'
  icases Hrs0' with ⟨-, #Hsc0⟩
  ihave #Hrs1' := Hrs1
  iunfold ownRS at Hrs1'
  icases Hrs1' with ⟨-, #Hsc1⟩
  -- half 0: its witness's index, if it replicates to it
  wp_bind (If (Val #em.rs0.rep) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(em.rs0.rep || sharedWitness em)⌝ ∗
      shared_ptr ↦ sharedWitness em))) $$ [shared]
  · cases hrep : em.rs0.rep <;> wp_auto <;> iframe shared <;> ipureintro <;> rfl
  iintro %v ⟨%Hv, shared⟩
  subst Hv
  generalize Hb0 : (em.rs0.rep || sharedWitness em) = b0 at *
  wp_join iprop(∃ (res1 : GMap w64 w64),
      "Hrm" ∷ rm ↦$ res1 ∗
      "Htrk" ∷ trk ↦ tv ∗ "Hin" ∷ ownIdsetQ vin (DFrac.own 1) V0 ∗
      "Hpm" ∷ ownProgressMap tv.Progress' pvs ∗
      "p" ∷ p_ptr ↦ trk ∗ "epoch" ∷ epoch_ptr ↦ tv.Epoch' ∗ "result" ∷ result_ptr ↦ rm ∗
      "indexer" ∷ indexer_ptr ↦ tracker.scopedAckIndexer.mk
        (interface.mkOk tracker.matchAckIndexer.ty #tv.Progress') r0.NonWitnessVoters' ∗
      "%Hres1" ∷ ⌜(∀ w, (res1 !! w).isSome = true ↔ (b0 = true ∧ em.rs0.wit = w)) ∧
         (∀ w N, res1 !! w = some N → CountGe V0 (rsAcked pvs em.rs0) (witnessRegularCount V0 em.rs0.rep) N)⌝)
    with [Hrm Htrk Hin Hpm p epoch result indexer w1]
  · -- half 0 does not replicate to a witness
    iexists ∅
    iframe Hrm Htrk Hin Hpm p epoch result indexer
    ipureintro
    rename_i Hif
    refine ⟨fun w => ?_, fun w N h => by simp at h⟩
    simp only [GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨h, -⟩; simp_all
  · -- Record the index supported by the incoming half.
    ihave #Hsi := scopedAckIndexer_isAckedIndexer wp_scopedAckIndexer_AckedIndex
      ⟨interface.mkOk tracker.matchAckIndexer.ty #tv.Progress', r0.NonWitnessVoters'⟩ _ _ _
      $$ Hpkg Hm Hsc0
    wp_pures
    -- `&p.Config.Voters[0]`, out of the tracker
    icases (Access.access
        (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
          tv.Config'.Voters')
        (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
          tv.Config'.Voters')
        (P := trk ↦ tv)) $$ Htrk with ⟨Hvf, Htrkback⟩
    icases array_acc_same (GF := GF) _ (sint.Z (W64 0)) _ _ _ vin (by decide) (by simp [Harr])
      $$ Hvf with ⟨Hv0, Hv0back⟩
    wp_auto
    ihave Hvf := Hv0back $$ Hv0
    ihave Htrk := Htrkback $$ Hvf
    wp_apply wp_witnessIndex V0 vin _ _ (scopedAcked em.rs0.nwv (pvsAcked pvs)) em.rs0.rep
      $$ [$Hin $Hsi $Hpm] as %N0 ⟨Hin, Hpm, %HC0⟩
    · ipureintro; exact Hsz0
    wp_pures
    wp_apply wp_mapInsert $$ Hrm as Hrm
    wp_join_done
    iexists _
    iframe Hrm Htrk Hin Hpm p epoch result indexer
    ipureintro
    refine ⟨fun w => ?_, fun w N h => ?_⟩
    · by_cases hw : em.rs0.wit = w
      · subst hw; simp
      · rw [GMap.lookup_insert_ne _ _ hw]; simp [hw]
    · by_cases hw : em.rs0.wit = w
      · subst hw
        rw [GMap.lookup_insert_eq] at h
        cases h
        exact HC0
      · rw [GMap.lookup_insert_ne _ _ hw] at h; simp at h
  iintro ⟨%res1, H⟩
  iNamed H
  obtain ⟨Hd1, Hc1⟩ := Hres1
  wp_auto
  -- half 1: its witness's index, the smaller one if the witness is half 0's too
  wp_bind (If (Val #em.rs1.rep) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(em.rs1.rep || sharedWitness em)⌝ ∗
      shared_ptr ↦ sharedWitness em))) $$ [shared]
  · cases hrep : em.rs1.rep <;> wp_auto <;> iframe shared <;> ipureintro <;> rfl
  iintro %v ⟨%Hv, shared⟩
  subst Hv
  generalize Hb1 : (em.rs1.rep || sharedWitness em) = b1 at *
  wp_join iprop(∃ (res2 : GMap w64 w64) (iv : tracker.scopedAckIndexer),
      "Hrm" ∷ rm ↦$ res2 ∗
      "Htrk" ∷ trk ↦ tv ∗ "Hout" ∷ ownIdsetQ vout (DFrac.own 1) V1 ∗
      "Hpm" ∷ ownProgressMap tv.Progress' pvs ∗
      "p" ∷ p_ptr ↦ trk ∗ "epoch" ∷ epoch_ptr ↦ tv.Epoch' ∗ "result" ∷ result_ptr ↦ rm ∗
      "indexer" ∷ indexer_ptr ↦ iv ∗
      "%Hres2" ∷ ⌜(∀ w, (res2 !! w).isSome = true ↔
          ((b0 = true ∧ em.rs0.wit = w) ∨ (b1 = true ∧ em.rs1.wit = w))) ∧
         (∀ w N, res2 !! w = some N →
           (b0 = true → em.rs0.wit = w → CountGe V0 (rsAcked pvs em.rs0) (witnessRegularCount V0 em.rs0.rep) N) ∧
           (b1 = true → em.rs1.wit = w → CountGe V1 (rsAcked pvs em.rs1) (witnessRegularCount V1 em.rs1.rep) N))⌝)
    with [Hrm Htrk Hout Hpm p epoch result indexer w2]
  · -- half 1 does not replicate to a witness
    iexists res1, _
    iframe Hrm Htrk Hout Hpm p epoch result indexer
    ipureintro
    refine ⟨fun w => ?_, fun w N h => ⟨fun h0 hw => Hc1 w N h, fun h1 => by simp at h1⟩⟩
    rw [Hd1 w]; simp
  · -- Merge the outgoing half's index with any existing index for this witness.
    ihave #Hsi1 := scopedAckIndexer_isAckedIndexer wp_scopedAckIndexer_AckedIndex
      ⟨interface.mkOk tracker.matchAckIndexer.ty #tv.Progress', r1.NonWitnessVoters'⟩ _ _ _
      $$ Hpkg Hm Hsc1
    icases (Access.access
        (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
          tv.Config'.Voters')
        (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦
          tv.Config'.Voters')
        (P := trk ↦ tv)) $$ Htrk with ⟨Hvf, Htrkback⟩
    icases array_acc_same (GF := GF) _ (sint.Z (W64 1)) _ _ _ vout (by decide) (by simp [Harr])
      $$ Hvf with ⟨Hv1, Hv1back⟩
    wp_auto
    ihave Hvf := Hv1back $$ Hv1
    ihave Htrk := Htrkback $$ Hvf
    wp_apply wp_witnessIndex V1 vout _ _ (scopedAcked em.rs1.nwv (pvsAcked pvs)) em.rs1.rep
      $$ [$Hout $Hsi1 $Hpm] as %N1 ⟨Hout, Hpm, %HC1⟩
    · ipureintro; exact Hsz1
    wp_pures
    wp_apply wp_map_lookup2 _ _ rm res1 em.rs1.wit $$ [$Hrm] as Hrm
    cases hl : res1 !! em.rs1.wit with
    | none =>
      simp only [Option.getD_none, Option.isSome_none]
      wp_auto
      wp_apply wp_mapInsert $$ Hrm as Hrm
      wp_join_done
      iexists _, _
      iframe Hrm Htrk Hout Hpm p epoch result indexer
      ipureintro
      refine ⟨fun w => ?_, fun w N h => ?_⟩
      · by_cases hw : em.rs1.wit = w
        · subst hw; simp
        · rw [GMap.lookup_insert_ne _ _ hw, Hd1 w]; simp [hw]
      · by_cases hw : em.rs1.wit = w
        · subst hw
          rw [GMap.lookup_insert_eq] at h
          cases h
          refine ⟨fun h0 hw0 => ?_, fun _ _ => HC1⟩
          exfalso
          have := (Hd1 em.rs1.wit).2 ⟨h0, hw0⟩
          rw [hl] at this; simp at this
        · rw [GMap.lookup_insert_ne _ _ hw] at h
          exact ⟨fun _ _ => Hc1 w N h, fun _ hw1 => absurd hw1 hw⟩
    | some idx1 =>
      simp only [Option.getD_some, Option.isSome_some]
      wp_auto
      wp_if_destruct
      · -- smaller than half 0's: replace it
        wp_pures
        wp_apply wp_mapInsert $$ Hrm as Hrm
        wp_join_done
        iexists _, _
        iframe Hrm Htrk Hout Hpm p epoch result indexer
        ipureintro
        refine ⟨fun w => ?_, fun w N h => ?_⟩
        · by_cases hw : em.rs1.wit = w
          · subst hw; simp
          · rw [GMap.lookup_insert_ne _ _ hw, Hd1 w]; simp [hw]
        · by_cases hw : em.rs1.wit = w
          · subst hw
            rw [GMap.lookup_insert_eq] at h
            cases h
            refine ⟨fun _ _ => (Hc1 _ idx1 hl).mono (by omega), fun _ _ => HC1⟩
          · rw [GMap.lookup_insert_ne _ _ hw] at h
            exact ⟨fun _ _ => Hc1 w N h, fun _ hw1 => absurd hw1 hw⟩
      · -- not smaller: keep half 0's
        wp_join_done
        iexists _, _
        iframe Hrm Htrk Hout Hpm p epoch result indexer
        ipureintro
        refine ⟨fun w => ?_, fun w N h => ?_⟩
        · by_cases hw : em.rs1.wit = w
          · subst hw; simp [hl]
          · rw [Hd1 w]; simp [hw]
        · by_cases hw : em.rs1.wit = w
          · subst hw
            rw [hl] at h
            cases h
            refine ⟨fun _ _ => Hc1 _ idx1 hl, fun _ _ => HC1.mono (by omega)⟩
          · exact ⟨fun _ _ => Hc1 w N h, fun _ hw1 => absurd hw1 hw⟩
  iintro ⟨%res2, %iv, H⟩
  iNamed H
  obtain ⟨Hd2, Hc2⟩ := Hres2
  wp_auto
  iapply HΦ
  iframe Htrk
  isplitl [Hin Hout Hpm]
  · iright
    iunfold oltqRes
    isplitr
    · ipureintro; rfl
    iexists vin, vout
    iframe Hin Hout Hpm
    ipureintro; exact ⟨Harr, Hsz0, Hsz1⟩
  iright
  isplitr
  · ipureintro; exact Hnone
  iexists res2
  iframe Hrm
  ipureintro
  subst Hb0 Hb1
  refine ⟨fun w => (Hd2 w).trans ?_, Hc2⟩
  by_cases hs : em.rs0.wit ≠ W64 0 ∧ em.rs0.wit = em.rs1.wit
  · have hsh : sharedWitness em = true := decide_eq_true hs
    rcases Hsome with hr | hr <;> simp only [hsh, Bool.or_true, true_and, hs.2, hr] <;> grind
  · have hsh : sharedWitness em = false := decide_eq_false hs
    simp only [hsh, Bool.or_false]
  done

end proof

end EtcdGrove
end Perennial
