/-
`shared.AddReadonlyTXID`, `shared.RemoveReadonlyTXID` (U2 internal), over the `readonlyTXIDs` field.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `shared`'s `readonlyTXIDs` at `s`: the readers' txids `ro`. -/
def roOwn (s : Loc) (ro : List w64) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef shared go!"readonlyTXIDs" s ↦ sl ∗ sl ↦* ro ∗
    ownSliceCap w64 sl (DFrac.own 1))

abbrev shared.AddReadonlyTXID.spec : Prop :=
  ∀ (s : Loc) (ro : List w64) (tid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ roOwn s ro }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"AddReadonlyTXID" #s)) (Val #tid))
  {{ RET #(); roOwn s (ro ++ [tid]) }}

theorem shared.AddReadonlyTXID.wp_proof : shared.AddReadonlyTXID.spec (GF := GF) (hG := hG) := by
  intro s ro tid
  wp_start as Hro
  iunfold roOwn at Hro
  icases Hro with ⟨%sl, Hf, Hsl, Hcap⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [Hsl Hcap Hsl1] as %s' ⟨Hro, Hro_cap, -⟩
  · iframe
  wp_auto
  iapply HΦ
  iunfold roOwn
  iexists s'
  iframe

abbrev shared.RemoveReadonlyTXID.spec : Prop :=
  ∀ (s : Loc) (ro : List w64) (tid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ roOwn s ro }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"RemoveReadonlyTXID" #s)) (Val #tid))
  {{ RET #(); ∃ ro', roOwn s ro' ∗ ⌜ro'.Perm (ro.erase tid)⌝ }}

theorem shared.RemoveReadonlyTXID.wp_proof :
    shared.RemoveReadonlyTXID.spec (GF := GF) (hG := hG) := by
  intro s ro tid
  wp_start as Hro0
  iunfold roOwn at Hro0
  icases Hro0 with ⟨%sl, Hf, Hro, Hro_cap⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hro
  ihave %Hswf := ownSlice_wf _ _ _ $$ Hro
  wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  ihave IH : iprop(∃ (k gi : w64), "i" ∷ i_ptr ↦ k ∗ "Hgi" ∷ gi_ptr ↦ gi ∗
      "Hro" ∷ sl ↦* ro ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ro.length : Int) ∧
        ∀ j < sint.nat k, ro[j]? ≠ some tid⌝) $$ [i Hgi Hro]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun j hj => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat k < ro.length := by word
    list_elem ro (sint.nat k) as e
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z k) ro _ e Hk.1 $$ [Hro] with Hro
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z k) ro _ e Hk.1 $$ [Hro] with Hro
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    wp_if_destruct
    · have Hlast : ro.length - 1 < ro.length := by omega
      list_elem ro (ro.length - 1) as y
      have hli : sint.Z (sl.len - W64 1) = (ro.length - 1 : Nat) := by word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_load_slice_index _ (sint.Z (sl.len - W64 1)) ro _ y
        (by word) $$ [Hro] with Hro
      · iframe; ipureintro; rw [hli]; exact Hy_lookup
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_store_slice_index _ (sint.Z k) ro y $$ [Hro] as Hro
      · iframe; ipureintro; exact ⟨Hk.1, by word⟩
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
      icases (ownSlice_split_all (sl.len - W64 1) _ _ _
        ⟨by word, by word⟩).1 $$ Hro with ⟨Hro, Hro2⟩
      ihave Hro_cap := ownSlice_slice_absorb_capacity _ _ (W64 0) (sl.len - W64 1)
        ⟨by decide, by word, by word⟩ $$ [Hro2 Hro_cap]
      · iframe
      try wp_auto
      wp_for_post
      try wp_auto
      have h : ((ro.set (sint.Z k).toNat y).take
          (sint.nat (sl.len - W64 1))).Perm (ro.erase tid) := by
        rw [Hif] at He_lookup
        have h := swapRemove_perm He_lookup Hk.2.2
        have hy : ro.getD (ro.length - 1) 0 = y := by
          simp [List.getD_eq_getElem?_getD, Hy_lookup]
        rw [hy] at h
        rw [show sint.nat (sl.len - W64 1) = ro.length - 1 by word]
        exact h
      iapply HΦ
      iexists _
      isplitl
      · iunfold roOwn; iexists _; iframe
      · ipureintro; exact h
    · wp_for_post
      iframe
      iexists k + W64 1, k
      iframe
      ipureintro
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      refine ⟨by word, by word, fun j hj => ?_⟩
      rw [hk1] at hj
      rcases Nat.lt_or_ge j (sint.nat k) with h | h
      · exact Hk.2.2 j h
      · rw [show j = sint.nat k by omega, He_lookup]; exact fun h => Hif (Option.some.inj h)
  · have Hnot : tid ∉ ro := by
      intro hm
      obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hm
      exact Hk.2.2 j (by word) (by rw [List.getElem?_eq_getElem hj, e])
    iapply HΦ
    iexists ro
    isplitl
    · iunfold roOwn; iexists sl; iframe
    · ipureintro; rw [List.erase_of_not_mem Hnot]

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
