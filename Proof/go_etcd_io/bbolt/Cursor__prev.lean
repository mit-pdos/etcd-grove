module
public import Spec.go_etcd_io.bbolt.Cursor__prev
public import Proof.go_etcd_io.bbolt.CursorLemmas
public import Spec.go_etcd_io.bbolt.Cursor__first
public import Spec.go_etcd_io.bbolt.Cursor__last
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
theorem Cursor.prev.wp_proof
    (hfirst : Cursor.first.spec (GF := GF) (hG := hG))
    (hlast : Cursor.last.spec (GF := GF) (hG := hG))
    (hkv : Cursor.keyValue.spec (GF := GF) (hG := hG)) :
    Cursor.prev.spec (GF := GF) (hG := hG) := by
  intro cl bl V q es Hok Hwf Hcur
  wp_start as Hc
  unfold curI
  icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have h00 : sint.Z (W64 0) = 0 := rfl
  have Hi0 : (sint.Z (cv.stack'.len - W64 1) + 1).toNat = es.length ∧
      -1 ≤ sint.Z (cv.stack'.len - W64 1) ∧ sint.Z (cv.stack'.len - W64 1) < es.length ∧
      (es ≠ [] → 0 ≤ sint.Z (cv.stack'.len - W64 1)) := by
    obtain ⟨h1, h2⟩ := Hsl
    have : es ≠ [] → 0 < es.length := fun h => List.length_pos_iff.2 h
    unfold sint.nat at h1
    refine ⟨?_, ?_, ?_, fun h => ?_⟩
    · word
    · word
    · word
    · have := this h; word
  wp_auto
  ihave IH : iprop(∃ (cv : Cursor) (i : w64),
      "i" ∷ i_ptr ↦ i ∗ "c" ∷ c_ptr ↦ cl ∗
      "%Hi" ∷ ⌜cv.bucket' = bl ∧ -1 ≤ sint.Z i ∧ sint.Z i < es.length ∧
        (es ≠ [] → 0 ≤ sint.Z i)⌝ ∗
      "Hcl" ∷ cl ↦ cv ∗ "Hs" ∷ cv.stack' ↦* es.take (sint.Z i + 1).toNat ∗
      "Hcap" ∷ ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ "Hctx" ∷ bktCtx bl V ∗
      "Hpgs" ∷ bktPages V q) $$ [i c Hcl Hs Hcap Hctx Hpgs]
  · iexists cv, _
    rw [Hi0.1, List.take_length]
    iframe
    ipureintro; exact ⟨Hb, Hi0.2⟩
  clear Hb Hsl Hi0
  wp_for IH
  obtain ⟨Hb, Him1, Hilt, Hipos⟩ := Hi
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_if_destruct
  · have Hi0 : 0 ≤ sint.Z i := by word
    have Hne : es ≠ [] := by intro h; subst h; simp at Hilt; omega
    have Hil : (sint.Z i).toNat < es.length := by omega
    have Hn1 : (sint.Z i + 1).toNat = (sint.Z i).toNat + 1 := by omega
    have Hlen1 : sint.Z cv.stack'.len = sint.Z i + 1 := by
      obtain ⟨h1, h2⟩ := Hsl
      rw [List.length_take_of_le (by omega)] at h1
      rw [show sint.nat cv.stack'.len = (sint.Z cv.stack'.len).toNat from rfl] at h1
      omega
    rw [Hn1]
    obtain ⟨r, pg, pid', Hcp, Hfl⟩ := Hcur.resolve_left Hne
    obtain ⟨pidi, pgi, Hbri, Htopi, Hnext⟩ := curPath_at V V.root pid' es r pg Hcp _ Hil
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi0, by omega⟩)]
    obtain ⟨Hwfi, Hnodei, Hpai, Hkindi⟩ := Htopi
    have Hcnti : pageCount pgi < 65536 := by have := leAt_lt pgi 10 2; unfold pageCount; omega
    icases ownSlice_elem_acc (sint.Z i) es[(sint.Z i).toNat] _ _ (es.take ((sint.Z i).toNat + 1)) Hi0
      (take_succ_getElem? es _ Hil) $$ Hs with ⟨Hr, Hsback⟩
    try wp_auto
    wp_if_destruct
    · -- `elem.index > 0`: one back, and down to the last leaf under it
      try wp_auto
      wp_for_post
      ihave Hs := Hsback $$ %({ es[(sint.Z i).toNat] with index' := es[(sint.Z i).toNat].index' - W64 1 } : elemRef) Hr
      rw [take_succ_set es _ _ Hil]
      have Hlen0 : cv.stack'.len ≠ W64 0 := fun h => by rw [h] at Hlen1; omega
      rw [decide_eq_false Hlen0]
      try wp_auto
      have Hidx : sint.Z (es[(sint.Z i).toNat].index' - W64 1) = sint.Z es[(sint.Z i).toNat].index' - 1 :=
        sint_pred _ (by omega)
      have Hcp2 : curPath V V.root (es.take (sint.Z i).toNat ++
          [{ es[(sint.Z i).toNat] with index' := es[(sint.Z i).toNat].index' - W64 1 }]) pidi
          { es[(sint.Z i).toNat] with index' := es[(sint.Z i).toNat].index' - W64 1 } pgi := by
        refine ⟨_, rfl, Hbri, Hwfi, Hnodei, Hpai, ?_⟩
        show (_ ∧ 0 ≤ sint.Z (es[(sint.Z i).toNat].index' - W64 1) ∧ _) ∨ _
        rw [Hidx]
        rcases Hkindi with ⟨Hb', Hi0', Hil'⟩ | ⟨Hl', Hli1, Hli2⟩
        · exact Or.inl ⟨Hb', by omega, by omega⟩
        · exact Or.inr ⟨Hl', by unfold leafIdx; rw [Hidx]; omega⟩
      wp_apply hlast cl bl V q _ pidi _ pgi Hok Hcp2 $$ [Hcl Hs Hcap Hctx Hpgs]
        as %es3 %r3 %pg3 ⟨%Hlt, Hc⟩
      · unfold curI
        iexists _
        iframe
        ipureintro; exact Hb
      unfold curI
      icases Hc with ⟨%cv3, %Hb3, Hcl, Hs, Hcap, Hctx, Hpgs⟩
      obtain ⟨pid3, pre3, Hes3, -, -, Hpa3, Hn3, Hlen3, Hfl3, Hlw3, Hli3, Hc3⟩ :=
        leafTop_facts V es3 r3 pg3 Hok Hlt
      icases bktPages_acc V q pid3 _ pg3 Hok Hpa3 $$ Hpgs with ⟨Hpg, Hpgsback⟩
      try wp_auto
      wp_apply hkv cl cv3 (DFrac.own 1) es3 (DFrac.own 1) r3 (DFrac.own q) pg3 (by rw [Hes3]; simp)
        Hn3 Hc3 Hlen3 Hfl3 Hlw3 (Hli3.2.imp_right (·.2)) $$ [Hcl Hs Hpg] as ⟨Hcl, Hs, Hpg⟩
      · iframe
      ispecialize Hpgsback $$ Hpg
      try wp_auto
      iapply HΦ
      isplitl []
      · ipureintro
        exact ⟨Or.inr ⟨r3, pg3, Hlt⟩, fun _ => by rw [Hes3]; simp, Or.inr ⟨r3, pg3, Hlt, rfl⟩⟩
      iexists cv3
      iframe
      ipureintro; exact Hb3
    · -- the first element of its page: up the stack
      ihave Hs := Hsback $$ %es[(sint.Z i).toNat] Hr
      rw [take_succ_set_self es _ Hil]
      try wp_auto
      by_cases Hi00 : sint.Z i = 0
      · have Hl1 : cv.stack'.len = W64 1 := w64_of_sint _ 1 (by omega) (by omega) (by omega)
        rw [decide_eq_true Hl1]
        try wp_auto
        wp_apply hfirst cl bl V q _ Hok Hwf $$ [Hcl Hs Hcap Hctx Hpgs] as %es3 %k3 %v3 %f3 ⟨%Hf3, Hc⟩
        · unfold curI
          iexists _
          iframe
          ipureintro; exact Hb
        try wp_auto
        wp_for_post
        ispecialize HΦ $$ %es3 %slice.nil %slice.nil %(W32 0)
        iapply HΦ
        isplitl []
        · ipureintro
          exact ⟨Hf3.1, fun _ => Hf3.2.1, Or.inl ⟨rfl, rfl, rfl⟩⟩
        unfold curI
        iexact Hc
      · have Hl1 : cv.stack'.len ≠ W64 1 := fun h => by rw [h] at Hlen1; have : sint.Z (W64 1) = 1 := rfl; omega
        rw [decide_eq_false Hl1]
        try wp_auto
        ihave %Hwfs := ownSlice_wf _ _ _ $$ Hs
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
        icases ownSlice_slice_with_cap (W64 0) i cv.stack' _ ⟨by omega, by omega, by omega⟩ $$ [Hs Hcap]
          with ⟨-, Hs, Hcap⟩
        · iframe
        have hn0 : sint.nat (W64 0) = 0 := rfl
        have Hni : sint.nat i = (sint.Z i).toNat := rfl
        rw [hn0, Hni, subslice_take_succ]
        try wp_auto
        wp_for_post
        iframe
        iexists _, (i - W64 1)
        have Him : sint.Z (i - W64 1) = sint.Z i - 1 := sint_pred i (by omega)
        rw [Him, show (sint.Z i - 1 + 1).toNat = (sint.Z i).toNat by omega]
        iframe
        ipureintro; exact ⟨Hb, by omega, by omega, fun _ => by omega⟩
  · -- `i = -1`: the stack is empty
    have Hm : sint.Z i = -1 := by word
    have Hes : es = [] := by
      refine Classical.byContradiction fun h => ?_
      have := Hipos h; omega
    subst Hes
    rw [Hm]
    simp only [List.take_nil]
    have Hl0 : cv.stack'.len = W64 0 := by
      obtain ⟨h1, h2⟩ := Hsl
      simp at h1; unfold sint.nat at h1; word
    rw [decide_eq_true Hl0]
    try wp_auto
    iapply HΦ
    iframe
    ipureintro; exact ⟨⟨Or.inl rfl, fun h => absurd rfl h, Or.inl ⟨rfl, rfl, rfl⟩⟩, Hb⟩

end proof

end bbolt
end EtcdGrove
end Perennial
