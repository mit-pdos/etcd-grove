/-
Proof of `Spec/ringBuffer__RemoveLess.lean` (etcd-io/etcd#21676). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__RemoveLess
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__moduloIndex
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__findFirstIndexGreaterOrEqual
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__RebaseHistory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- For sorted revisions, the items with revision `≥ rv` are those after the
`ltCount` items below it: `RemoveLess`'s `findFirstIndexGreaterOrEqual` finds where they
start. -/
theorem removeLessItems_eq_drop {V : Type} (revOf : V → w64) (rv : w64) :
    ∀ items : List V, RevSorted revOf items →
      removeLessItems revOf rv items = items.drop (ltCount revOf rv items)
  | [], _ => rfl
  | a :: rest, h => by
    unfold RevSorted at h
    rw [List.pairwise_cons] at h
    obtain ⟨ha, hrest⟩ := h
    by_cases hlt : sint.Z (revOf a) < sint.Z rv
    · have ih := removeLessItems_eq_drop revOf rv rest hrest
      unfold removeLessItems ltCount at ih ⊢
      rw [List.filter_cons_of_neg (by simp; omega), List.countP_cons_of_pos (by simpa using hlt),
        List.drop_succ_cons]
      exact ih
    · have hall : ∀ b ∈ a :: rest, sint.Z rv ≤ sint.Z (revOf b) := by
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · omega
        · have := ha b hb; omega
      unfold removeLessItems ltCount
      rw [List.filter_eq_self.2 (fun b hb => by simpa using hall b hb),
        List.countP_eq_zero.2 (fun b hb => by have := hall b hb; simp; omega)]
      rfl

theorem ringBuffer.RemoveLess.wp_proof
    (wp_moduloIndex : ringBuffer.moduloIndex.spec (GF := GF) (hG := hG))
    (wp_findFirstIndexGreaterOrEqual :
      ringBuffer.findFirstIndexGreaterOrEqual.spec (GF := GF) (hG := hG))
    (wp_RebaseHistory : ringBuffer.RebaseHistory.spec (GF := GF) (hG := hG)) :
    ringBuffer.RemoveLess.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items rv
  wp_start as H
  iNamed H
  wp_auto
  have Hsorted0 := Hsorted
  have Hs := Hok.size
  wp_if_destruct
  · -- empty: nothing to drop
    have Hnil : items = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    subst Hnil
    rw [show removeLessItems revOf rv ([] : List V) = [] from rfl]
    iapply HΦ
    iapply ownRingBuffer_intro r cap isItem revOf [] rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf
  ihave H := ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf
  iclear Hitems HrevOf
  have Hpos : 0 < items.length := by
    have : sint.Z rb.size' ≠ 0 := by word
    omega
  clear Hok Hrev Hsorted rb ents Hs Hif
  wp_apply wp_findFirstIndexGreaterOrEqual $$ [$H] as H
  rw [removeLessItems_eq_drop revOf rv items Hsorted0]
  ihave %Hn := ownRingBuffer_length r cap isItem revOf items $$ H
  have Hk := ltCount_le revOf rv items
  have Hkw : sint.Z (W64 (ltCount revOf rv items : Int)) = ltCount revOf rv items := by
    have := Hn.2; word
  have Hkw' : sint.Z (BitVec.ofNat 64 (ltCount revOf rv items)) = ltCount revOf rv items := by
    have := Hn.2; word
  wp_if_destruct
  · -- nothing below `rv`
    have H0 : ltCount revOf rv items = 0 := by rw [Hkw] at Hif; word
    rw [H0, List.drop_zero]
    iapply HΦ $$ H
  have Hk0 : 0 < ltCount revOf rv items := by rw [Hkw] at Hif; word
  clear Hif
  iNamed H
  wp_auto
  have Hs := Hok.size
  wp_if_destruct
  · -- everything is below `rv`
    have Hall : ltCount revOf rv items = items.length := by
      have := congrArg sint.Z Hif; rw [Hkw, Hs] at this; omega
    rw [Hall, List.drop_length]
    ihave H := ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf
    wp_apply wp_RebaseHistory $$ [$H] as H
    iapply HΦ $$ H
  have Hlt : ltCount revOf rv items < items.length := by
    have : ltCount revOf rv items ≠ items.length := by
      intro h; apply Hif; apply BitVec.eq_of_toInt_eq
      show sint.Z _ = sint.Z _
      rw [Hkw, Hs, h]
    omega
  clear Hif
  have Hc := Hok.cap_pos
  have Hc2 := Hok.cap_le
  have Hl := Hok.len
  have Ht := Hok.tail_lt
  have Hsl := Hok.size_le
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have Hel : ents.length = cap := by have := Hlen.1; word
  -- `j` slots zeroed; those of the items kept (from index `k` on) are untouched
  ihave HI : iprop(∃ (j key : w64) (ents' : List (entry T')),
      "Hri" ∷ «$range_i_ptr» ↦ j ∗
      "i" ∷ i_ptr ↦ key ∗
      "Hr" ∷ r ↦ rb ∗
      "Hbuf" ∷ rb.buffer' ↦* ents' ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ltCount revOf rv items ∧ ents'.length = cap ∧
        ∀ m, ltCount revOf rv items ≤ m → m < items.length →
          ents'[ringSlot rb.tail' cap m]? = ents[ringSlot rb.tail' cap m]?⌝)
      $$ [«$range_i» i Hr Hbuf]
  · iexists W64 0, zero_val w64, ents
    simp only [named]
    iframe
    ipureintro
    exact ⟨by word, by word, Hel, fun _ _ _ => trivial⟩
  wp_for HI
  cleanup_bool_decide
  wp_if_destruct
  · -- zero the slot of logical index `j`
    have Hjk : sint.Z j < ltCount revOf rv items := by simp at Hif; rw [Hkw'] at Hif; exact Hif
    have Hm1 : -sint.Z rb.buffer'.len ≤ sint.Z (rb.tail' + j) := by word
    have Hm2 : sint.Z (rb.tail' + j) + sint.Z rb.buffer'.len < 2 ^ 63 := by word
    wp_apply wp_moduloIndex $$ [Hr] as Hr
    · iframe Hr; ipureintro; exact ⟨by omega, Hm1, Hm2⟩
    rw [Hl, ringSlot_sint rb.tail' j cap Hc Hc2 Ht ⟨Hj.1, by omega⟩]
    have Hslot : ringSlot rb.tail' cap (sint.nat j) < cap := Nat.mod_lt _ Hc
    rw [ite_eq_left (by omega)]
    wp_apply wp_store_slice_index rb.buffer' _ ents' _ $$ [Hbuf] as Hbuf
    · iframe Hbuf; ipureintro; omega
    wp_for_post
    iframe
    iexists j + W64 1, j, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hj.2.2.1], fun m hm1 hm2 => ?_⟩
    rw [Int.toNat_natCast, List.getElem?_set_ne]
    · exact Hj.2.2.2 m hm1 hm2
    · intro h
      have := mod_inj_of_lt _ cap (sint.nat j) m (by word) (by omega) h
      word
  · -- all `k` slots zeroed: move `tail` past them
    have Hjk : sint.Z j = ltCount revOf rv items := by simp at Hif; rw [Hkw'] at Hif; omega
    have Hm1 : -sint.Z rb.buffer'.len ≤ sint.Z (rb.tail' + W64 (ltCount revOf rv items : Int)) := by
      word
    have Hm2 : sint.Z (rb.tail' + W64 (ltCount revOf rv items : Int)) + sint.Z rb.buffer'.len <
        2 ^ 63 := by word
    wp_apply wp_moduloIndex $$ [Hr] as Hr
    · iframe Hr; ipureintro; exact ⟨by omega, Hm1, Hm2⟩
    wp_auto
    try dsimp only at *
    generalize Ht'def :
      W64 (sint.Z (rb.tail' + W64 (ltCount revOf rv items : Int)) % sint.Z rb.buffer'.len) = t'
    iapply HΦ
    have Hk61 := Hn.2
    have Htk : sint.Z (rb.tail' + W64 (ltCount revOf rv items : Int)) =
        ((sint.nat rb.tail' + ltCount revOf rv items : Nat) : Int) := by word
    have Ht' : sint.Z t' = (((sint.nat rb.tail' + ltCount revOf rv items) % cap : Nat) : Int) := by
      rw [← Ht'def, Htk, Hl, ← Int.natCast_emod]
      have : (sint.nat rb.tail' + ltCount revOf rv items) % cap < cap := Nat.mod_lt _ Hc
      generalize (sint.nat rb.tail' + ltCount revOf rv items) % cap = m at this ⊢
      word
    have Htn' : sint.nat t' = (sint.nat rb.tail' + ltCount revOf rv items) % cap := by
      simp only [sint.nat, Ht', Int.toNat_natCast]
    have Hslot' : ∀ i, ringSlot t' cap i = ringSlot rb.tail' cap (ltCount revOf rv items + i) := by
      intro i; simp only [ringSlot]; rw [Htn', Nat.mod_add_mod, Nat.add_assoc]
    have Hn' : (items.drop (ltCount revOf rv items)).length =
        items.length - ltCount revOf rv items := List.length_drop
    have Hok' : RingOk (T' := T')
        { buffer' := rb.buffer', head' := rb.head', tail' := t',
          size' := rb.size' - W64 (ltCount revOf rv items : Int), revisionOf' := rb.revisionOf' }
        cap (items.drop (ltCount revOf rv items)).length := by
      rw [Hn']
      have Hm := Nat.mod_lt (sint.nat rb.tail' + ltCount revOf rv items) Hc
      refine ⟨Hc, Hc2, Hl, ?_, by omega, ?_, ?_⟩ <;> dsimp only
      · word
      · rw [Ht']; constructor <;> omega
      · rw [Hok.head, Ht', show sint.Z rb.tail' = ((sint.nat rb.tail' : Nat) : Int) by word]
        have key : ((sint.nat rb.tail' + ltCount revOf rv items) % cap +
            (items.length - ltCount revOf rv items)) % cap =
            (sint.nat rb.tail' + items.length) % cap := by
          rw [Nat.mod_add_mod]; congr 1; omega
        rw [← Int.natCast_add, ← Int.natCast_add, ← Int.natCast_emod, ← Int.natCast_emod, key]
    have Hkept : ∀ (i : Nat) (w : V), (items.drop (ltCount revOf rv items))[i]? = some w →
        items[ltCount revOf rv items + i]? = some w ∧
          ents'[ringSlot t' cap i]? = ents[ringSlot rb.tail' cap (ltCount revOf rv items + i)]? := by
      intro i w Hw
      rw [List.getElem?_drop] at Hw
      have Hlt' := (List.getElem?_eq_some_iff.1 Hw).1
      refine ⟨Hw, ?_⟩
      rw [Hslot']
      exact Hj.2.2.2 _ (by omega) Hlt'
    have Hrev' : ∀ (i : Nat) (w : V), (items.drop (ltCount revOf rv items))[i]? = some w →
        ∃ e, ents'[ringSlot t' cap i]? = some e ∧ e.revision' = revOf w := by
      intro i w Hw
      obtain ⟨Hi, He⟩ := Hkept i w Hw
      rw [He]
      exact Hrev _ w Hi
    iapply ownRingBuffer_intro r cap isItem revOf _ _ _ Hok' Hrev'
      (Hsorted.sublist (List.drop_sublist _ _)) $$ Hr Hbuf [] HrevOf
    imodintro
    iintro %i %w %e %Hw %He
    obtain ⟨Hi, He'⟩ := Hkept i w Hw
    rw [He'] at He
    iapply Hitems $$ %_ %w %e %Hi %He

end proof

end EtcdGrove
end Perennial
