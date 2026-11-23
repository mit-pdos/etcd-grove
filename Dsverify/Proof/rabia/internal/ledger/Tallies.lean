/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Tallies.lean`, run `rabia-r1wake-1`.)

The `sort.Interface` of `tallies` (`Len`, `Less`, `Swap`): a sorter of the tallies a slice holds,
by `tallyLt`.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Sorting

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.ledger.Assumptions]

/-- The tallies slice `ps` holds `xs` (each count an `int`). -/
def ownTallies (ps : GoSlice) (xs : List (ObjV × Nat)) : IProp GF :=
  iprop(∃ tl : List Tally, "Hpsl" ∷ ps ↦* tl ∗ "#Htl" ∷ talliesRep tl xs ∗
    "%Hcnt" ∷ ⌜∀ x ∈ xs, cntOk x.2⌝)

theorem talliesRep_len (tl : List Tally) (xs : List (ObjV × Nat)) :
    talliesRep (GF := GF) tl xs ⊢ ⌜tl.length = xs.length⌝ := by
  unfold talliesRep; iintro ⟨%H, -⟩; ipureintro; exact H

theorem ownSlice_halves {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (vs : List V) :
    (s ↦* vs : IProp GF) ⊣⊢ s ↦*{DFrac.own (1 : Qp).half} vs ∗ s ↦*{DFrac.own (1 : Qp).half} vs := by
  have hq : (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half := by
    rw [show DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half =
      DFrac.own ((1 : Qp).half + (1 : Qp).half) from rfl, Qp.half_add_half]
  conv => lhs; rw [hq]
  exact (ownSlice_dfractional s vs).dfractional _ _

theorem talliesRep_lookup (tl : List Tally) (xs : List (ObjV × Nat)) (k : Nat) (t : Tally)
    (x : ObjV × Nat) (ht : tl[k]? = some t) (hx : xs[k]? = some x) :
    talliesRep (GF := GF) tl xs ⊢ tallyRep t x := by
  unfold talliesRep; iintro ⟨-, #H⟩; iapply H $$ %k %t %x %ht %hx

theorem objRep_ids (v : ConsensusObj) (o : ObjV) :
    objRep (GF := GF) v o ⊢ ⌜v.ProId' = o.proId ∧ v.ProSeq' = o.proSeq⌝ := by
  iintro H; icases objRep_fields v o $$ H with %H; ipureintro; exact ⟨H.1, H.2.1⟩

theorem tally_split (l : Loc) (t : Tally) (dq : DFrac) :
    typedPointsto (GF := GF) l t dq ⊣⊢ ⌜l ≠ null⌝ ∗
      typedPointsto (structFieldRef Tally go!"Proposal" l) t.Proposal' dq ∗
      typedPointsto (structFieldRef Tally go!"Count" l) t.Count' dq := by
  constructor
  · iintro H
    icases typedPointsto_not_null_dup _ _ _ $$ H with ⟨H, %hnn⟩
    iStructNamed H
    iframe Proposal Count
    ipureintro; exact hnn
  · iintro ⟨%h, H1, H2⟩
    iapply typedPointsto_combine _ _ _ h
    simp only [TypedPointsto.typedPointstoDef]
    iframe H1 H2

theorem tallies_restore (ps : GoSlice) (tl : List Tally) (ti tj : Tally) (i j : Int)
    (hti : tl[i.toNat]? = some ti) (htj : tl[j.toNat]? = some tj)
    (hni : sliceIndexRef Tally i ps ≠ null) (hnj : sliceIndexRef Tally j ps ≠ null) :
    ⊢ (∀ v', sliceIndexRef Tally i ps ↦{DFrac.own (1 : Qp).half} v' -∗
        ps ↦*{DFrac.own (1 : Qp).half} tl.set i.toNat v') -∗
      (∀ v', sliceIndexRef Tally j ps ↦{DFrac.own (1 : Qp).half} v' -∗
        ps ↦*{DFrac.own (1 : Qp).half} tl.set j.toNat v') -∗
      typedPointsto (GF := GF) (structFieldRef Tally go!"Proposal" (sliceIndexRef Tally i ps))
        ti.Proposal' (DFrac.own (1 : Qp).half) -∗
      typedPointsto (structFieldRef Tally go!"Count" (sliceIndexRef Tally i ps))
        ti.Count' (DFrac.own (1 : Qp).half) -∗
      typedPointsto (structFieldRef Tally go!"Proposal" (sliceIndexRef Tally j ps))
        tj.Proposal' (DFrac.own (1 : Qp).half) -∗
      typedPointsto (structFieldRef Tally go!"Count" (sliceIndexRef Tally j ps))
        tj.Count' (DFrac.own (1 : Qp).half) -∗
      ps ↦* tl := by
  iintro Hp1 Hp2 Hpi Hci Hpj Hcj
  ihave Hi := (tally_split _ ti _).2 $$ [Hpi Hci]
  · iframe Hpi Hci; ipureintro; exact hni
  ihave Hj := (tally_split _ tj _).2 $$ [Hpj Hcj]
  · iframe Hpj Hcj; ipureintro; exact hnj
  ihave H1 := Hp1 $$ Hi
  ihave H2 := Hp2 $$ Hj
  rw [list_set_lookup_self _ _ _ hti, list_set_lookup_self _ _ _ htj]
  iapply (ownSlice_halves ps tl).2
  iframe H1 H2

theorem tallies_wp_Len (ps : GoSlice) (xs : List (ObjV × Nat)) :
    {{ ownTallies (GF := GF) ps xs }}
      (App (Val #(methods tallies.ty go!"Len" #ps)) (Val #()))
    {{ RET #(W64 xs.length); ownTallies ps xs }} := by
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hpsl
  ihave %Hlen := talliesRep_len _ _ $$ Htl
  have he : ps.len = W64 xs.length := by word
  rw [he]
  iapply HΦ
  unfold ownTallies
  iexists tl
  iframe Hpsl Htl
  ipureintro; exact Hcnt

theorem tallies_wp_Less (wp_Lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG))
    (ps : GoSlice) (l : List (ObjV × Nat)) (i j : w64) (a b : ObjV × Nat)
    (h : 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ ownTallies (GF := GF) ps l }}
      (App (App (Val #(methods tallies.ty go!"Less" #ps)) (Val #i)) (Val #j))
    {{ (r : Bool), RET #r; ownTallies ps l ∗ ⌜r = true ↔ tallyLt a b = true⌝ }} := by
  wp_start as H
  iNamed H
  obtain ⟨hi, hj, ha, hb⟩ := h
  ihave %Hl := ownSlice_len _ _ _ $$ Hpsl
  ihave %Hlen := talliesRep_len _ _ $$ Htl
  have hil : sint.Z i < sint.Z ps.len := by
    have := (List.getElem?_eq_some_iff.1 ha).1; word
  have hjl : sint.Z j < sint.Z ps.len := by
    have := (List.getElem?_eq_some_iff.1 hb).1; word
  list_elem tl (sint.nat i) as ti
  list_elem tl (sint.nat j) as tj
  icases (ownSlice_halves ps tl).1 $$ Hpsl with ⟨Hp1, Hp2⟩
  have hti : tl[(sint.Z i).toNat]? = some ti := by
    rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hti_lookup
  have htj : tl[(sint.Z j).toNat]? = some tj := by
    rw [show (sint.Z j).toNat = sint.nat j by word]; exact Htj_lookup
  icases ownSlice_elem_acc (sint.Z i) ti ps _ tl hi hti $$ Hp1 with ⟨Hi, Hp1⟩
  icases ownSlice_elem_acc (sint.Z j) tj ps _ tl hj htj $$ Hp2 with ⟨Hj, Hp2⟩
  icases (tally_split _ _ _).1 $$ Hi with ⟨%hni, Hpi, Hci⟩
  icases (tally_split _ _ _).1 $$ Hj with ⟨%hnj, Hpj, Hcj⟩
  ihave #Hti := talliesRep_lookup tl l (sint.nat i) ti a Hti_lookup ha $$ Htl
  ihave #Htj := talliesRep_lookup tl l (sint.nat j) tj b Htj_lookup hb $$ Htl
  unfold tallyRep
  icases Hti with ⟨#Hoi, %Hci⟩
  icases Htj with ⟨#Hoj, %Hcj⟩
  ihave %Hidi := objRep_ids _ _ $$ Hoi
  ihave %Hidj := objRep_ids _ _ $$ Hoj
  have hca := Hcnt a (List.mem_of_getElem? ha)
  have hcb := Hcnt b (List.mem_of_getElem? hb)
  wp_auto
  repeat (simp only [hi, hil, hj, hjl, and_self, ↓reduceIte]; wp_auto)
  ihave Hps := tallies_restore ps tl ti tj (sint.Z i) (sint.Z j) hti htj hni hnj
  have hca' : sint.Z ti.Count' = (a.2 : Int) := by rw [Hci]; unfold cntOk at hca; word
  have hcb' : sint.Z tj.Count' = (b.2 : Int) := by rw [Hcj]; unfold cntOk at hcb; word
  wp_if_destruct
  · iapply HΦ
    iframe
    isplitl
    · unfold ownTallies; iexists tl
      iframe Htl
      isplitl
      · iapply Hps $$ Hp1 Hp2 Hpi Hci Hpj Hcj
      · ipureintro; exact Hcnt
    · ipureintro; simp only [true_iff, tallyLt_iff]; omega
  · repeat (simp only [hi, hil, hj, hjl, and_self, ↓reduceIte]; wp_auto)
    wp_if_destruct
    · repeat (simp only [hi, hil, hj, hjl, and_self, ↓reduceIte]; wp_auto)
      wp_apply wp_Lt $$ [$Hpi $Hpj] as ⟨Hpi, Hpj⟩
      iapply HΦ
      isplitl
      · unfold ownTallies; iexists tl
        iframe Htl
        isplitl
        · iapply Hps $$ Hp1 Hp2 Hpi Hci Hpj Hcj
        · ipureintro; exact Hcnt
      · ipureintro
        have hq : ti.Count' = tj.Count' := Hif
        have heq : a.2 = b.2 := by
          have := congrArg (fun w => sint.Z w) hq; omega
        rw [decide_eq_true_iff, tallyLt_iff, Hidi.2, Hidj.2, Hidi.1, Hidj.1]
        have hs : a.1.proSeq = b.1.proSeq ↔ a.1.proSeq.toNat = b.1.proSeq.toNat :=
          ⟨fun h => by rw [h], fun h => BitVec.eq_of_toNat_eq h⟩
        rw [hs]; omega
    · iapply HΦ
      isplitl
      · unfold ownTallies; iexists tl
        iframe Htl
        isplitl
        · iapply Hps $$ Hp1 Hp2 Hpi Hci Hpj Hcj
        · ipureintro; exact Hcnt
      · ipureintro
        have hne : ¬ a.2 = b.2 := by
          intro h; apply Hif; apply BitVec.eq_of_toInt_eq
          have := hca'; have := hcb'; simp only [sint.Z] at *; omega
        simp only [Bool.false_eq_true, false_iff, tallyLt_iff]; omega

theorem swap_lookup {α : Type} (l : List α) (i j k : Nat) (x y z : α) (hx : l[i]? = some x)
    (hy : l[j]? = some y) (h : ((l.set i y).set j x)[k]? = some z) :
    (k = j ∧ z = x) ∨ (k ≠ j ∧ k = i ∧ z = y) ∨ (k ≠ j ∧ k ≠ i ∧ l[k]? = some z) := by
  have hil := (List.getElem?_eq_some_iff.1 hx).1
  have hjl := (List.getElem?_eq_some_iff.1 hy).1
  rw [List.getElem?_set, List.getElem?_set] at h
  by_cases hkj : j = k
  · subst hkj; simp at h; exact Or.inl ⟨rfl, h.2.symm⟩
  · rw [ite_eq_right hkj] at h
    by_cases hki : i = k
    · subst hki; rw [ite_eq_left rfl, ite_eq_left hil] at h; cases h; exact Or.inr (Or.inl ⟨Ne.symm hkj, rfl, rfl⟩)
    · rw [ite_eq_right hki] at h; exact Or.inr (Or.inr ⟨Ne.symm hkj, Ne.symm hki, h⟩)

theorem talliesRep_swap (tl : List Tally) (l : List (ObjV × Nat)) (i j : Nat) (ti tj : Tally)
    (a b : ObjV × Nat) (hti : tl[i]? = some ti) (htj : tl[j]? = some tj) (ha : l[i]? = some a)
    (hb : l[j]? = some b) :
    talliesRep (GF := GF) tl l ⊢ talliesRep ((tl.set i tj).set j ti) ((l.set i b).set j a) := by
  unfold talliesRep
  iintro ⟨%Hlen, #H⟩
  isplitr
  · ipureintro; simp [Hlen]
  · iintro !> %k %t %x %Ht %Hx
    rcases swap_lookup tl i j k ti tj t hti htj Ht with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rcases swap_lookup l i j k a b x ha hb Hx with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;>
    (try omega)
    · rw [h2, g2]; iapply H $$ %i %ti %a %hti %ha
    · rw [h3, g3]; iapply H $$ %j %tj %b %htj %hb
    · iapply H $$ %k %t %x %h3 %g3

theorem tallies_wp_Swap (ps : GoSlice) (l : List (ObjV × Nat)) (i j : w64) (a b : ObjV × Nat)
    (h : 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ l[sint.nat i]? = some a ∧ l[sint.nat j]? = some b) :
    {{ ownTallies (GF := GF) ps l }}
      (App (App (Val #(methods tallies.ty go!"Swap" #ps)) (Val #i)) (Val #j))
    {{ RET #(); ownTallies ps ((l.set (sint.nat i) b).set (sint.nat j) a) }} := by
  wp_start as H
  iNamed H
  obtain ⟨hi, hj, ha, hb⟩ := h
  ihave %Hl := ownSlice_len _ _ _ $$ Hpsl
  ihave %Hlen := talliesRep_len _ _ $$ Htl
  have hil : sint.Z i < sint.Z ps.len := by
    have := (List.getElem?_eq_some_iff.1 ha).1; word
  have hjl : sint.Z j < sint.Z ps.len := by
    have := (List.getElem?_eq_some_iff.1 hb).1; word
  list_elem tl (sint.nat i) as ti
  list_elem tl (sint.nat j) as tj
  have hti : tl[(sint.Z i).toNat]? = some ti := by
    rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hti_lookup
  have htj : tl[(sint.Z j).toNat]? = some tj := by
    rw [show (sint.Z j).toNat = sint.nat j by word]; exact Htj_lookup
  wp_auto
  repeat (simp only [hi, hil, hj, hjl, and_self, ↓reduceIte]; wp_auto)
  simp only [hj, hjl, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index ps (sint.Z j) tl _ tj hj $$ [$Hpsl] as Hpsl
  · ipureintro; exact htj
  simp only [hi, hil, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index ps (sint.Z i) tl _ ti hi $$ [$Hpsl] as Hpsl
  · ipureintro; exact hti
  wp_apply wp_store_slice_index ps (sint.Z i) tl tj $$ [$Hpsl] as Hpsl
  · ipureintro; constructor <;> word
  wp_apply wp_store_slice_index ps (sint.Z j) _ ti $$ [$Hpsl] as Hpsl
  · ipureintro; simp only [List.length_set]; constructor <;> word
  iapply HΦ
  unfold ownTallies
  iexists ((tl.set (sint.nat i) tj).set (sint.nat j) ti)
  rw [show (sint.Z i).toNat = sint.nat i by word, show (sint.Z j).toNat = sint.nat j by word]
  iframe Hpsl
  isplitl
  · iapply talliesRep_swap tl l _ _ ti tj a b Hti_lookup Htj_lookup ha hb $$ Htl
  · ipureintro
    intro x hx
    rcases List.mem_iff_getElem?.1 hx with ⟨k, hk⟩
    rcases swap_lookup l _ _ k a b x ha hb hk with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · subst h; exact Hcnt _ (List.mem_of_getElem? ha)
    · subst h; exact Hcnt _ (List.mem_of_getElem? hb)
    · exact Hcnt _ (List.mem_of_getElem? h)

theorem talliesRep_set (tl : List Tally) (l : List (ObjV × Nat)) (i : Nat) (t : Tally)
    (x : ObjV × Nat) :
    talliesRep (GF := GF) tl l ∗ tallyRep t x ⊢ talliesRep (tl.set i t) (l.set i x) := by
  unfold talliesRep
  iintro ⟨⟨%Hlen, #H⟩, #Ht⟩
  isplitr
  · ipureintro; simp [Hlen]
  · iintro !> %k %t' %x' %Ht' %Hx'
    rw [List.getElem?_set] at Ht' Hx'
    by_cases hk : i = k
    · subst hk
      simp only [↓reduceIte] at Ht' Hx'
      split at Ht'
      · rename_i hlt
        rw [if_pos (by omega)] at Hx'
        cases Ht'; cases Hx'; iexact Ht
      · cases Ht'
    · simp only [hk, ↓reduceIte] at Ht' Hx'
      iapply H $$ %k %t' %x' %Ht' %Hx'

theorem talliesRep_app (tl : List Tally) (l : List (ObjV × Nat)) (t : Tally) (x : ObjV × Nat) :
    talliesRep (GF := GF) tl l ∗ tallyRep t x ⊢ talliesRep (tl ++ [t]) (l ++ [x]) := by
  unfold talliesRep
  iintro ⟨⟨%Hlen, #H⟩, #Ht⟩
  isplitr
  · ipureintro; simp [Hlen]
  · iintro !> %k %t' %x' %Ht' %Hx'
    rw [List.getElem?_append] at Ht' Hx'
    by_cases hk : k < tl.length
    · rw [if_pos hk] at Ht'
      rw [if_pos (by omega)] at Hx'
      iapply H $$ %k %t' %x' %Ht' %Hx'
    · rw [if_neg hk] at Ht'
      rw [if_neg (by omega)] at Hx'
      rw [Hlen] at Ht'
      have hk' : k - l.length = 0 := by
        rcases Nat.lt_or_ge (k - l.length) 1 with h | h
        · omega
        · simp [List.getElem?_eq_none_iff.2 (by simp; omega : [t].length ≤ k - l.length)] at Ht'
      rw [hk'] at Ht' Hx'
      cases Ht'; cases Hx'; iexact Ht

/-- **`tallies(ps)` sorts the tallies `ps` holds by `tallyLt`.** -/
theorem tallies_isSorter (wp_Lt : ProxySeqIdLessThan.spec (GF := GF) (hG := hG)) (ps : GoSlice) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ⊢
      sort.isSorter (interface.mk tallies.ty #ps) (ownTallies ps)
        (fun a b => tallyLt a b = true) := by
  iintro #Hpkg
  iapply sort.isSorter_intro
  isplitr
  · iintro !> %l' %Φ' !> Hown HΦ'
    iapply tallies_wp_Len $$ Hown HΦ'
  isplitr
  · iintro !> %l' %i %j %a %b %Hij %Φ' !> Hown HΦ'
    iapply tallies_wp_Less wp_Lt ps l' i j a b Hij $$ [Hown] HΦ'
    iframe Hpkg Hown
  · iintro !> %l' %i %j %a %b %Hij %Φ' !> Hown HΦ'
    iapply tallies_wp_Swap ps l' i j a b Hij $$ Hown HΦ'

end proof
end Perennial.rabia.internal.ledger
