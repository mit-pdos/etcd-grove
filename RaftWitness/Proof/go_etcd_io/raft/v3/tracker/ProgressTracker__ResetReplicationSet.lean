/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/ProgressTracker__ResetReplicationSet.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ResetReplicationSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The tracker's `Config.Witnesses[i]`, out and back. -/
theorem trk_wit_acc (trk : Loc) (tv : tracker.ProgressTracker) (i : Int) (w : w64)
    (hpos : 0 ≤ i) (hlookup : tv.Config'.Witnesses'.arr[i.toNat]? = some w) :
    (trk ↦ tv : IProp GF) ⊢
      arrayIndexRef w64 i trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Witnesses"] ↦ w ∗
      (arrayIndexRef w64 i trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Witnesses"] ↦ w -∗
        trk ↦ tv) := by
  iintro Htrk
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Witnesses"] ↦
        tv.Config'.Witnesses')
      (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Witnesses"] ↦
        tv.Config'.Witnesses')
      (P := trk ↦ tv)) $$ Htrk with ⟨Hwf, Hback⟩
  icases array_acc_same (GF := GF) _ i _ _ _ w hpos hlookup $$ Hwf with ⟨Hw, Hwback⟩
  iframe Hw
  iintro Hw
  iapply Hback
  iapply Hwback $$ Hw

theorem ownRSb_intro (V : GSet w64) (w x : w64) (mref : Loc) (mv : GMap w64 Unit)
    (Hx : x = if w ∈ V then w else W64 0) (Hd : domSet mv = V \ {[w]}) :
    (mref ↦$ mv : IProp GF) ⊢ ownRSb (tracker.ReplicationSet.mk x x mref) (rsReset V w) := by
  iintro Hm
  unfold ownRSb rsReset
  isplitr
  · ipureintro; exact ⟨Hx, Hx⟩
  iexists mv
  iframe Hm
  ipureintro; exact Hd

/-- An empty half's voter map. -/
theorem reset_empty (w : w64) :
    W64 0 = (if w ∈ (∅ : GSet w64) then w else W64 0) ∧
      domSet (∅ : GMap w64 Unit) = (∅ : GSet w64) \ {[w]} := by
  refine ⟨(if_neg (not_elem_of_empty w)).symm, ?_⟩
  rw [GMap.dom_empty]
  apply set_eq; intro k
  rw [elem_of_difference]
  constructor
  · intro h; exact absurd h (not_elem_of_empty k)
  · intro h; exact absurd h.1 (not_elem_of_empty k)

/-- The fresh epoch's subterm (`0`, or the old one's plus one); with no witness the early return;
else the range over the two halves, each building its replication set by a range over its
voters, then the install; the epoch and its maps are frozen at the end. -/
theorem tracker.ProgressTracker.ResetReplicationSet.wp_proof :
    tracker.ProgressTracker.ResetReplicationSet.spec (GF := GF) (hG := hG) := by
  intro trk tv b vin vout dqv V0 V1 w0 w1 sub Harr Hwit
  wp_start as ⟨Htrk, Hin, Hout, Hsub⟩
  wp_auto
  -- `if !resetSubterm { epoch.Subterm = p.Epoch.Subterm + 1 }`
  wp_bind (If (Val #(!b)) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ trk ↦ tv ∗ p_ptr ↦ trk ∗
      epoch_ptr ↦ «$r0_ptr» ∗ «$r0_ptr» ↦ tracker.Epoch.mk (if b then W64 0 else sub + W64 1)
        (zero_val (GoArray tracker.ReplicationSet 2))))) $$ [Htrk p epoch «$r0» Hsub]
  · cases b
    · icases Hsub with (%Hf | #Hsub)
      · cases Hf
      wp_auto
      iframe
      ipureintro; rfl
    · wp_auto
      iframe
      ipureintro; rfl
  iintro %v ⟨%Hv, Htrk, p, epoch, «$r0»⟩
  subst Hv
  wp_auto
  icases trk_wit_acc trk tv (sint.Z (W64 0)) w0 (by decide) (by simp [Hwit]) $$ Htrk with ⟨Hw, Hback⟩
  wp_auto
  ihave Htrk := Hback $$ Hw
  by_cases Hnw : w0 = W64 0 ∧ w1 = W64 0
  · -- no witness: the bare epoch, installed
    obtain ⟨rfl, rfl⟩ := Hnw
    wp_auto
    icases trk_wit_acc trk tv (sint.Z (W64 1)) (W64 0) (by decide) (by simp [Hwit]) $$ Htrk
      with ⟨Hw, Hback⟩
    wp_auto
    ihave Htrk := Hback $$ Hw
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #He
    wp_auto
    iapply HΦ
    iframe Htrk Hin Hout
    rw [resetEpoch_nw]
    iapply ownEpoch_bare_intro _ _ _ rfl rfl $$ He
  -- a witness: the condition is false
  wp_bind (If (Val #(decide (w0 = W64 0))) _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #false⌝ ∗ trk ↦ tv ∗ p_ptr ↦ trk))) $$ [Htrk p]
  · by_cases h0 : w0 = W64 0
    · have h1 : w1 ≠ W64 0 := fun h => Hnw ⟨h0, h⟩
      rw [decide_eq_true h0]
      wp_auto
      icases trk_wit_acc trk tv (sint.Z (W64 1)) w1 (by decide) (by simp [Hwit]) $$ Htrk
        with ⟨Hw, Hback⟩
      wp_auto
      ihave Htrk := Hback $$ Hw
      iframe Htrk p
      ipureintro; rw [decide_eq_false h1]
    · rw [decide_eq_false h0]
      wp_auto
      iframe Htrk p
      ipureintro; rfl
  iintro %v ⟨%Hv, Htrk, p⟩
  subst Hv
  wp_auto
  rename_i ii_ptr
  irename : (ii_ptr ↦ zero_val w64 : IProp GF) => ii
  icases epoch_split _ _ $$ «$r0» with ⟨%Hnn, Hsub, Hrs⟩
  -- `for i, c := range p.Voters`: the halves before `j` built
  ihave HI : (∃ (j iv : w64) (cv : quorum.MajorityConfig) (arr : GoArray tracker.ReplicationSet 2),
      "i" ∷ i_ptr ↦ j ∗ "ii" ∷ ii_ptr ↦ iv ∗ "c" ∷ c_ptr ↦ cv ∗
      "Hrs" ∷ «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ arr ∗
      "Htrk" ∷ trk ↦ tv ∗ "p" ∷ p_ptr ↦ trk ∗ "epoch" ∷ epoch_ptr ↦ «$r0_ptr» ∗
      "Hin" ∷ ownIdsetQ vin dqv V0 ∗ "Hout" ∷ ownIdsetQ vout dqv V1 ∗
      "Hj" ∷ (⌜j = W64 0 ∧ arr.arr = [zero_val _, zero_val _]⌝ ∨
        (⌜j = W64 1⌝ ∗ ∃ r0, ⌜arr.arr = [r0, zero_val _]⌝ ∗ ownRSb r0 (rsReset V0 w0)) ∨
        (⌜j = W64 2⌝ ∗ ∃ r0 r1, ⌜arr.arr = [r0, r1]⌝ ∗ ownRSb r0 (rsReset V0 w0) ∗
          ownRSb r1 (rsReset V1 w1))) : IProp GF) $$ [i ii c Hrs Htrk p epoch Hin Hout]
  · iexists W64 0, _, _, _
    iframe i ii c Hrs Htrk p epoch Hin Hout
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_for HI
  icases Hj with (⟨%Hj, %Ha⟩ | ⟨%Hj, %r0, %Ha, Hr0⟩ | ⟨%Hj, %r0, %r1, %Ha, Hr0, Hr1⟩)
  · subst Hj
    wp_if_destruct <;> try (exfalso; word)
    wp_func_lits
    rw [Harr]
    simp only [List.getElem?_cons_zero]
    wp_auto
    icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ arr (zero_val _) (by decide) (by rw [Ha]; rfl)
      $$ Hrs with ⟨Hel, Hrsback⟩
    wp_auto
    wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
    unfold ownIdsetQ
    icases Hin with (⟨%Hnil, %Hs⟩ | Hin)
    · -- no voters: nothing to range over
      subst Hnil Hs
      wp_func_lits
      wp_auto
      wp_for_post
      simp only [named]
      iframe HΦ Hsub
      iexists W64 0 + W64 1, W64 0, map.nil,
        array.mk 2 (arr.arr.set (sint.Z (W64 0)).toNat (tracker.ReplicationSet.mk (W64 0) (W64 0) mref))
      ihave Hrs := Hrsback $$ %(tracker.ReplicationSet.mk (W64 0) (W64 0) mref) Hel
      iframe i ii c Hrs Htrk p epoch Hout
      isplitl []
      · ileft; ipureintro; simp
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists tracker.ReplicationSet.mk (W64 0) (W64 0) mref
      isplitr
      · ipureintro; rw [Ha]; rfl
      iapply ownRSb_intro _ _ _ _ _ (reset_empty w0).1 (reset_empty w0).2 $$ Hmref
    wp_func_lits
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x xw : w64)
        (mv : GMap w64 Unit),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "%Hxw" ∷ ⌜xw = if w0 ∈ keys.take i.toNat then w0 else W64 0⌝ ∗
        "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ keys.take i.toNat ∧ k ≠ w0⌝ ∗
        "id" ∷ id_ptr ↦ x ∗
        "Hel" ∷ arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ tracker.ReplicationSet.mk xw xw mref ∗
        "Hmref" ∷ mref ↦$ mv ∗ "Htrk" ∷ trk ↦ tv ∗ "p" ∷ p_ptr ↦ trk ∗
        "ii" ∷ ii_ptr ↦ W64 0 ∗
        "set" ∷ set_ptr ↦ arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"])) $$ Hin
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [id Hel Hmref Htrk p ii set]
    · iexists zero_val w64, W64 0, ∅
      simp only [named]
      iframe id Hel Hmref Htrk p ii set
      ipureintro
      refine ⟨Int.le_refl _, ?_, fun k => ?_⟩
      · simp
      · rw [GMap.dom_empty]
        simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, _root_.false_and]
        exact iff_false_intro (not_elem_of_empty k)
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      icases trk_wit_acc trk tv (sint.Z (W64 0)) w0 (by decide) (by simp [Hwit]) $$ Htrk
        with ⟨Hw, Hback⟩
      wp_auto
      ihave Htrk := Hback $$ Hw
      have Hst := reset_step keys i key w0 mv Hi Hkey Hmv
      wp_if_destruct
      · -- the witness: `set.Excluded = id; set.Witness = id`
        have Heq := Hif
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists key, w0, mv
        simp only [named]
        rw [← Heq]
        iframe id Hel Hmref Htrk p ii set
        ipureintro
        refine ⟨by omega, ?_, (Hst.1 Heq.symm).1⟩
        rw [if_pos (Hst.1 Heq.symm).2]
      · -- `set.NonWitnessVoters[id] = struct{}{}`
        have Hne := Hif
        wp_apply wp_mapInsert $$ Hmref as Hmref
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists key, xw, _
        simp only [named]
        iframe id Hel Hmref Htrk p ii set
        ipureintro
        have Hne' : key ≠ w0 := fun h => Hne h.symm
        refine ⟨by omega, ?_, (Hst.2 Hne').1⟩
        rw [Hxw]
        simp only [(Hst.2 Hne').2]
    iintro HP Hin
    iNamed HP
    rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv Hxw
    obtain ⟨Hd, Hmem⟩ := reset_done V0 w0 keys mv Hkset Hmv
    wp_for_post
    simp only [named]
    iframe HΦ Hsub
    iexists W64 0 + W64 1, W64 0, vin,
      array.mk 2 (arr.arr.set (sint.Z (W64 0)).toNat (tracker.ReplicationSet.mk xw xw mref))
    ihave Hrs := Hrsback $$ %(tracker.ReplicationSet.mk xw xw mref) Hel
    iframe i ii c Hrs Htrk p epoch Hout
    isplitl [Hin]
    · iright; iexact Hin
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists tracker.ReplicationSet.mk xw xw mref
    isplitr
    · ipureintro; rw [Ha]; rfl
    iapply ownRSb_intro _ _ _ _ _ (by rw [Hxw]; simp only [Hmem]) Hd $$ Hmref
  · subst Hj
    wp_if_destruct <;> try (exfalso; word)
    wp_func_lits
    rw [Harr]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
    wp_auto
    icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ arr (zero_val _) (by decide) (by rw [Ha]; rfl)
      $$ Hrs with ⟨Hel, Hrsback⟩
    wp_auto
    wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
    unfold ownIdsetQ
    icases Hout with (⟨%Hnil, %Hs⟩ | Hout)
    · -- no voters: nothing to range over
      subst Hnil Hs
      wp_func_lits
      wp_auto
      wp_for_post
      simp only [named]
      iframe HΦ Hsub
      iexists W64 1 + W64 1, W64 1, map.nil,
        array.mk 2 (arr.arr.set (sint.Z (W64 1)).toNat (tracker.ReplicationSet.mk (W64 0) (W64 0) mref))
      ihave Hrs := Hrsback $$ %(tracker.ReplicationSet.mk (W64 0) (W64 0) mref) Hel
      iframe i ii c Hrs Htrk p epoch Hin
      isplitl []
      · ileft; ipureintro; simp
      iright; iright
      isplitr
      · ipureintro; rfl
      iexists r0, tracker.ReplicationSet.mk (W64 0) (W64 0) mref
      isplitr
      · ipureintro; rw [Ha]; rfl
      iframe Hr0
      iapply ownRSb_intro _ _ _ _ _ (reset_empty w1).1 (reset_empty w1).2 $$ Hmref
    wp_func_lits
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x xw : w64)
        (mv : GMap w64 Unit),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "%Hxw" ∷ ⌜xw = if w1 ∈ keys.take i.toNat then w1 else W64 0⌝ ∗
        "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ keys.take i.toNat ∧ k ≠ w1⌝ ∗
        "id" ∷ id_ptr ↦ x ∗
        "Hel" ∷ arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ tracker.ReplicationSet.mk xw xw mref ∗
        "Hmref" ∷ mref ↦$ mv ∗ "Htrk" ∷ trk ↦ tv ∗ "p" ∷ p_ptr ↦ trk ∗
        "ii" ∷ ii_ptr ↦ W64 1 ∗
        "set" ∷ set_ptr ↦ arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"])) $$ Hout
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [id Hel Hmref Htrk p ii set]
    · iexists zero_val w64, W64 0, ∅
      simp only [named]
      iframe id Hel Hmref Htrk p ii set
      ipureintro
      refine ⟨Int.le_refl _, ?_, fun k => ?_⟩
      · simp
      · rw [GMap.dom_empty]
        simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, _root_.false_and]
        exact iff_false_intro (not_elem_of_empty k)
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      icases trk_wit_acc trk tv (sint.Z (W64 1)) w1 (by decide) (by simp [Hwit]) $$ Htrk
        with ⟨Hw, Hback⟩
      wp_auto
      ihave Htrk := Hback $$ Hw
      have Hst := reset_step keys i key w1 mv Hi Hkey Hmv
      wp_if_destruct
      · -- the witness: `set.Excluded = id; set.Witness = id`
        have Heq := Hif
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists key, w1, mv
        simp only [named]
        rw [← Heq]
        iframe id Hel Hmref Htrk p ii set
        ipureintro
        refine ⟨by omega, ?_, (Hst.1 Heq.symm).1⟩
        rw [if_pos (Hst.1 Heq.symm).2]
      · -- `set.NonWitnessVoters[id] = struct{}{}`
        have Hne := Hif
        wp_apply wp_mapInsert $$ Hmref as Hmref
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists key, xw, _
        simp only [named]
        iframe id Hel Hmref Htrk p ii set
        ipureintro
        have Hne' : key ≠ w1 := fun h => Hne h.symm
        refine ⟨by omega, ?_, (Hst.2 Hne').1⟩
        rw [Hxw]
        simp only [(Hst.2 Hne').2]
    iintro HP Hout
    iNamed HP
    rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv Hxw
    obtain ⟨Hd, Hmem⟩ := reset_done V1 w1 keys mv Hkset Hmv
    wp_for_post
    simp only [named]
    iframe HΦ Hsub
    iexists W64 1 + W64 1, W64 1, vout,
      array.mk 2 (arr.arr.set (sint.Z (W64 1)).toNat (tracker.ReplicationSet.mk xw xw mref))
    ihave Hrs := Hrsback $$ %(tracker.ReplicationSet.mk xw xw mref) Hel
    iframe i ii c Hrs Htrk p epoch Hin
    isplitl [Hout]
    · iright; iexact Hout
    iright; iright
    isplitr
    · ipureintro; rfl
    iexists r0, tracker.ReplicationSet.mk xw xw mref
    isplitr
    · ipureintro; rw [Ha]; rfl
    iframe Hr0
    iapply ownRSb_intro _ _ _ _ _ (by rw [Hxw]; simp only [Hmem]) Hd $$ Hmref
  · subst Hj
    -- `p.Epoch = epoch`: the halves and the epoch frozen
    rw [show decide (sint.Z (W64 2) < sint.Z (W64 2)) = false by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    imod ownRSb_persist _ _ $$ Hr0 with #Hr0
    imod ownRSb_persist _ _ $$ Hr1 with #Hr1
    ihave He := epoch_combine _ _ _ Hnn $$ [Hsub Hrs]
    · iframe Hsub Hrs
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ He with #He
    wp_auto
    iapply HΦ
    iframe Htrk Hin Hout
    unfold resetEpoch
    rw [if_neg Hnw]
    unfold ownEpoch
    iexists _, r0, r1
    iframe He Hr0 Hr1
    ipureintro; exact ⟨rfl, Ha⟩

end proof

end EtcdGrove
end Perennial
