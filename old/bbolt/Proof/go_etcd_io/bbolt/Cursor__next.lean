module
public import Spec.go_etcd_io.bbolt.Cursor__next
public import Proof.go_etcd_io.bbolt.CursorLemmas
public import Spec.go_etcd_io.bbolt.elemRef__count
public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack
public import Spec.go_etcd_io.bbolt.Cursor__keyValue

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxHeartbeats 400000 in
theorem Cursor.next.wp_proof
    (hcount : elemRef.count.spec (GF := GF) (hG := hG))
    (hgoto : Cursor.goToFirstElementOnTheStack.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue.spec (GF := GF) (hG := hG)) :
    Cursor.next.spec (GF := GF) (hG := hG) := by
  intro cl bl V q es0 Hok Hcur
  wp_start as Hc
  unfold curI
  icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  wp_auto
  ihave IH : iprop(∃ (cv : Cursor) (es : List elemRef),
      "c" ∷ c_ptr ↦ cl ∗ "%Hcp" ∷ ⌜cv.bucket' = bl ∧ cursorOK V es ∧ (es0 ≠ [] → es ≠ [])⌝ ∗
      "Hcl" ∷ cl ↦ cv ∗ "Hs" ∷ cv.stack' ↦* es ∗
      "Hcap" ∷ ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ "Hctx" ∷ bktCtx bl V q ∗
      "Hpgs" ∷ bktPages V q) $$ [c Hcl Hs Hcap Hctx Hpgs]
  · iexists cv, es0; iframe; ipureintro; exact ⟨Hb, Hcur, fun h => h⟩
  clear Hcur Hb
  wp_for IH
  obtain ⟨Hb, Hcur, Hne0⟩ := Hcp
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  try wp_auto
  ihave IH2 : iprop(∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜-1 ≤ sint.Z i ∧ sint.Z i < es.length⌝ ∗
      "Hcl" ∷ cl ↦ cv ∗ "Hs" ∷ cv.stack' ↦* es ∗ "Hpgs" ∷ bktPages V q ∗ "c" ∷ c_ptr ↦ cl)
    $$ [i Hcl Hs Hpgs c]
  · iexists _; iframe; ipureintro; constructor <;> word
  wp_for IH2
  wp_if_destruct
  · -- the element `i`
    have Hi0 : 0 ≤ sint.Z i := by word
    have Hne : es ≠ [] := by intro h; subst h; simp at Hi; word
    obtain ⟨r, pg, pid', Hcp, Hfl⟩ := Hcur.resolve_left Hne
    have Hil : (sint.Z i).toNat < es.length := by word
    have Hs1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
    have Hn : sint.nat (i + W64 1) = (sint.Z i).toNat + 1 := by word
    have HlenZ : sint.Z cv.stack'.len = (es.length : Int) := by word
    have h00 : sint.Z (W64 0) = 0 := rfl
    have hn0 : sint.nat (W64 0) = 0 := rfl
    obtain ⟨pidi, pgi, Hbri, Htopi, Hnext⟩ := curPath_at V V.root pid' es r pg Hcp _ Hil
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    obtain ⟨Hwfi, Hnodei, Hpai, Hkindi⟩ := Htopi
    have Hci := pageAt_car V pidi _ pgi Hok Hpai
    obtain ⟨p1, pg1, Hpa1, Hleni, -, -, -⟩ := wfAt_page V pidi Hok Hwfi
    obtain ⟨-, Hpg1⟩ := pageAt_unique Hpai Hpa1
    subst Hpg1
    icases ownSlice_elem_acc (sint.Z i) es[(sint.Z i).toNat] _ _ es (by word) (by simp) $$ Hs
      with ⟨Hr, Hsback⟩
    icases bktPages_acc V q pidi _ pgi Hok Hpai $$ Hpgs with ⟨Hpg, Hpgsback⟩
    try wp_auto
    wp_apply hcount _ es[(sint.Z i).toNat] (DFrac.own 1) (DFrac.own q) pgi Hnodei Hci Hleni
      $$ [Hr Hpg] as ⟨Hr, Hpg⟩
    · iframe
    ispecialize Hpgsback $$ Hpg
    try wp_auto
    have Hcnt : pageCount pgi < 65536 := by have := leAt_lt pgi 10 2; unfold pageCount; omega
    wp_if_destruct
    · rw [sub_one_sint _ Hcnt] at Hif
      try wp_auto
      wp_for_post
      have Hn1 : ¬ i = W64 (-1) := fun h => by rw [h] at Hi0; exact absurd Hi0 (by decide)
      rw [decide_eq_false Hn1]
      try wp_auto
      ihave Hs := Hsback $$ %({ es[(sint.Z i).toNat] with index' := es[(sint.Z i).toNat].index' + W64 1 } : elemRef) Hr
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
      icases ownSlice_slice_with_cap (W64 0) (i + W64 1) cv.stack' _ ⟨by omega, by omega, by omega⟩ $$ [Hs Hcap]
        with ⟨-, Hs, Hcap⟩
      · iframe
      rw [Hn, hn0, subslice_set_succ es _ _ Hil]
      try wp_auto
      have Hidx : sint.Z (es[(sint.Z i).toNat].index' + W64 1) = sint.Z es[(sint.Z i).toNat].index' + 1 :=
        sint_succ _ (by omega) (by
          rcases Hkindi with ⟨_, h, _⟩ | ⟨_, _, h⟩
          · omega
          · rcases h with h | ⟨h, _⟩ <;> omega)
      have Hcp2 : curPath V V.root (es.take (sint.Z i).toNat ++
          [{ es[(sint.Z i).toNat] with index' := es[(sint.Z i).toNat].index' + W64 1 }]) pidi
          { es[(sint.Z i).toNat] with index' := es[(sint.Z i).toNat].index' + W64 1 } pgi := by
        refine ⟨_, rfl, Hbri, Hwfi, Hnodei, Hpai, ?_⟩
        show (_ ∧ 0 ≤ sint.Z (es[(sint.Z i).toNat].index' + W64 1) ∧ _) ∨ _
        rw [Hidx]
        rcases Hkindi with ⟨Hb', Hi0', Hil'⟩ | ⟨Hl', Hli1, Hli2⟩
        · exact Or.inl ⟨Hb', by omega, by omega⟩
        · exact Or.inr ⟨Hl', by unfold leafIdx; rw [Hidx]; omega⟩
      wp_apply hgoto cl bl V q _ pidi _ pgi Hok Hcp2
        $$ [Hcl Hs Hcap Hctx Hpgsback]
        as %es3 %r3 %pg3 ⟨%Hlt, Hc⟩
      · unfold curI
        iexists _
        iframe
        ipureintro; exact Hb
      unfold curI
      icases Hc with ⟨%cv3, %Hb3, Hcl, Hs, Hcap, Hctx, Hpgs⟩
      obtain ⟨pid3, pre3, Hes3, Hbr3, Hwf3, Hpa3, Hn3, Hlen3, Hfl3, Hlw3, Hli3, Hc3⟩ :=
        leafTop_facts V es3 r3 pg3 Hok Hlt
      subst Hes3
      ihave %Hsl3 := ownSlice_len _ _ _ $$ Hs
      simp only [List.length_append, List.length_singleton] at Hsl3
      obtain ⟨Hix3, Hb3'⟩ := top_index cv3.stack' pre3.length Hsl3
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true Hb3')]
      icases ownSlice_elem_acc (sint.Z (cv3.stack'.len - W64 1)) r3 _ _ (pre3 ++ [r3]) Hb3'.1
        (by rw [Hix3]; simp) $$ Hs with ⟨Hr, Hsback⟩
      icases bktPages_acc V q pid3 _ pg3 Hok Hpa3 $$ Hpgs with ⟨Hpg, Hpgsback⟩
      wp_apply hcount _ r3 (DFrac.own 1) (DFrac.own q) pg3 Hn3 Hc3 Hlen3 $$ [Hr Hpg] as ⟨Hr, Hpg⟩
      · iframe
      ihave Hs := Hsback $$ %r3 Hr
      rw [Hix3, set_len_append]
      try wp_auto
      ispecialize Hpgsback $$ Hpg
      have Hcnt3 : pageCount pg3 < 65536 := by have := leAt_lt pg3 10 2; unfold pageCount; omega
      by_cases Hc0 : pageCount pg3 = 0
      · rw [decide_eq_true (by rw [Hc0]; rfl)]
        try wp_auto
        wp_for_post
        iframe
        iexists cv3, pre3 ++ [r3]
        iframe
        ipureintro; exact ⟨Hb3, Or.inr ⟨r3, pg3, Hlt⟩, fun _ => by simp⟩
      · rw [decide_eq_false (w64_nat_ne_zero _ (by omega) Hc0)]
        try wp_auto
        icases bktPages_acc V q pid3 _ pg3 Hok Hpa3 $$ Hpgsback with ⟨Hpg, Hpgsback⟩
        wp_apply hkv cl cv3 (DFrac.own 1) (pre3 ++ [r3]) (DFrac.own 1) r3 (DFrac.own q) pg3 (by simp)
          Hn3 Hc3 Hlen3 Hfl3 Hlw3 (Hli3.2.imp_right (·.2)) $$ [Hcl Hs Hpg] as ⟨Hcl, Hs, Hpg⟩
        · iframe
        ispecialize Hpgsback $$ Hpg
        try wp_auto
        wp_for_post
        iapply HΦ
        isplitl []
        · ipureintro; exact ⟨Or.inr ⟨r3, pg3, Hlt⟩, fun _ => by simp, Or.inr ⟨r3, pg3, Hlt, rfl⟩⟩
        iexists cv3
        iframe
        ipureintro; exact Hb3
    · try wp_auto
      wp_for_post
      ihave Hs := Hsback $$ %es[(sint.Z i).toNat] Hr
      rw [List.set_getElem_self]
      try wp_auto
      iframe
      iexists (i - W64 1)
      iframe
      ipureintro; constructor <;> word
  · have Hm1 : i = W64 (-1) := by word
    rw [decide_eq_true Hm1]
    try wp_auto
    wp_for_post
    iapply HΦ
    iframe
    isplitl []
    · ipureintro; exact ⟨Hcur, Hne0, Or.inl ⟨rfl, rfl, rfl⟩⟩
    ipureintro; exact Hb

end proof

end bbolt
end EtcdGrove
end Perennial
