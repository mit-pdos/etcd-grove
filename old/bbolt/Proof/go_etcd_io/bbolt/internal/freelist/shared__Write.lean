module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Write
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Count
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Copyall
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetCount
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.Write.wp_proof (hCount : shared.Count.spec (GF := GF) (hG := hG))
    (hCopy : shared.Copyall.spec (GF := GF) (hG := hG))
    (hSF : Page.SetFlags.spec (GF := GF) (hG := hG))
    (hSC : Page.SetCount.spec (GF := GF) (hG := hG))
    (hAdd : UnsafeAdd.spec (GF := GF) (hG := hG)) :
    shared.Write.spec (GF := GF) (hG := hG) := by
  intro I s σ p pv old hFC hFPI Hnn Hold
  wp_start as ⟨Hsh, Hown, Hp, Hsl⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases ownShared_wf _ _ _ $$ Hsh with ⟨Hsh, %Hwf⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have Hlen : σ.allIds.length < 2 ^ 63 := Hwf.2.2.2.1
  wp_auto
  wp_apply (hSF p pv (W16 16)) $$ [Hp] as Hp
  · iexact Hp
  try wp_auto
  wp_bind (App (Val #(methods (go.GoType.PointerType shared.ty) go!"Count" #s)) (Val #()))
  iapply (hCount I s σ hFC) $$ [Hsh Hown]
  · iframe; iexact Hpkg
  inext
  iintro ⟨Hsh, Hown⟩
  have Hc : (σ.free.length + σ.pendingCount : Nat) = σ.allIds.length := by
    unfold FLState.allIds FLState.pendingCount; rw [List.length_append]
  rw [Hc]
  try wp_auto
  by_cases H0 : σ.allIds.length = 0
  · rw [decide_eq_true (by rw [H0]; rfl)]
    try wp_auto
    wp_apply (hSC p _ _) $$ [Hp] as Hp
    · iexact Hp
    try wp_auto
    have Hnil : σ.allIds = [] := List.eq_nil_of_length_eq_zero H0
    have Hold0 : old = [] := List.eq_nil_of_length_eq_zero (by rw [Hold, H0]; rfl)
    subst Hold0
    ispecialize HΦ $$ %([] : List w64)
    iapply HΦ
    rw [if_neg (by omega)]
    iframe
    isplitr
    · ipureintro; rw [Hnil]; exact ⟨by simp [PgidsSorted], List.Perm.refl _⟩
    iExactEq Hp
    simp [flCount, H0]
    done
  · rw [decide_eq_false (by word)]
    try wp_auto
    by_cases Hsm : σ.allIds.length < 65535
    · rw [decide_eq_true (by word)]
      try wp_auto
      wp_apply (hSC p _ _) $$ [Hp] as Hp
      · iexact Hp
      try wp_auto
      wp_apply (hAdd p (W64 16))
      try wp_auto
      wp_func_call
      try wp_auto
      rw [decide_eq_false (by word)]
      try wp_auto
      rw [decide_eq_false (loc_add_ne_null p _ Hnn)]
      try wp_auto
      rw [show typeSize w64 = 8 from go.typeSize_w64]
      try wp_auto
      rw [decide_eq_false (by word)]
      try wp_auto
      have Hol : old.length = σ.allIds.length := by rw [Hold]; unfold flCells; rw [if_neg (by omega)]
      rw [show sint.Z (W64 16) = 16 by rfl]
      rw [Hol]
      wp_apply (hCopy I s σ _ old hFPI (by omega)) $$ [Hsh Hown Hsl] as %out ⟨%Hout, Hsl, Hsh, Hown⟩
      · iframe
      try wp_auto
      iapply HΦ
      rw [if_neg (by omega)]
      rw [show old.drop σ.allIds.length = [] from List.drop_eq_nil_of_le (by omega), List.append_nil]
      iframe
      isplitr
      · ipureintro; exact Hout
      iExactEq Hp
      simp [flCount, H0, Hsm]
      congr 2
      word
    · rw [decide_eq_false (by word)]
      have Hol : old.length = σ.allIds.length + 1 := by
        rw [Hold]; simp [flCells, show 65535 ≤ σ.allIds.length by omega]
      have Hn1 : σ.allIds.length + 1 < 2 ^ 63 := by
        have h := Hsll.2; simp only [Hol] at h; word
      try wp_auto
      wp_apply (hSC p _ _) $$ [Hp] as Hp
      · iexact Hp
      try wp_auto
      wp_apply (hAdd p (W64 16))
      try wp_auto
      wp_func_call
      try wp_auto
      rw [decide_eq_false (by word)]
      try wp_auto
      rw [decide_eq_false (loc_add_ne_null p _ Hnn)]
      try wp_auto
      rw [show typeSize w64 = 8 from go.typeSize_w64]
      try wp_auto
      by_cases Hbig : sint.Z (W64 ((2 ^ 63 - 1) / 8)) < sint.Z (W64 (σ.allIds.length : Int) + W64 1)
      · rw [decide_eq_true Hbig]
        try wp_auto
        wp_apply wp_AngelicExit
      rw [decide_eq_false Hbig]
      try wp_auto
      rw [show sint.Z (W64 16) = 16 by rfl]
      have Hw : W64 (σ.allIds.length : Int) + W64 1 = W64 (old.length : Int) := by rw [Hol]; word
      rw [Hw]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
      wp_apply wp_store_slice_index _ (sint.Z (W64 0)) old (W64 (σ.allIds.length : Int)) $$ [Hsl] as Hsl
      · iframe; ipureintro
        exact ⟨by word, by rw [Hol]; word⟩
      try wp_auto
      obtain ⟨o0, orest, rfl⟩ : ∃ o0 orest, old = o0 :: orest := by
        cases old with
        | nil => simp at Hol
        | cons o0 orest => exact ⟨o0, orest, rfl⟩
      have Hrl : orest.length = σ.allIds.length := by simp at Hol; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
      icases (ownSlice_split_all (W64 1) (slice.mk (p +ₗ 16) (W64 ((o0 :: orest).length : Int))
        (W64 ((o0 :: orest).length : Int))) _ _ ⟨by word, by word⟩).1 $$ Hsl with ⟨Hsl0, Hsl1⟩
      have e1 : sint.nat (W64 1) = 1 := rfl
      isimp only [e1, List.set_cons_zero, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
        List.drop_zero] at Hsl0 Hsl1
      try wp_auto
      wp_apply (hCopy I s σ _ orest hFPI (by omega)) $$ [Hsh Hown Hsl1] as %out ⟨%Hout, Hsl1, Hsh, Hown⟩
      · iframe
      try wp_auto
      rw [show orest.drop σ.allIds.length = [] from List.drop_eq_nil_of_le (by omega), List.append_nil]
      ihave Hsl : slice.mk (p +ₗ 16) (W64 ((o0 :: orest).length : Int))
          (W64 ((o0 :: orest).length : Int)) ↦* (W64 (σ.allIds.length : Int) :: out) $$ [Hsl0 Hsl1]
      · iapply (ownSlice_split_all (W64 1) _ _ _ ⟨by word, by word⟩).2
        simp only [e1, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
        iframe
      iapply HΦ
      rw [if_pos (by omega)]
      iframe
      isplitr
      · ipureintro; exact Hout
      iExactEq Hp
      simp [flCount, H0, Hsm]
      done

end proof

end bbolt
end EtcdGrove
end Perennial
