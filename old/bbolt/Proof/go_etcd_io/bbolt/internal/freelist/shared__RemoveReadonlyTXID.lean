module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__RemoveReadonlyTXID
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas

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

theorem shared.RemoveReadonlyTXID.wp_proof : shared.RemoveReadonlyTXID.spec (GF := GF) (hG := hG) := by
  intro s iface σ tid
  wp_start as Hs
  unfold ownShared ownSharedC
  icases Hs with ⟨%sv, %c, Hs, %Hok⟩
  iNamed Hs
  ihave %Hl := ownSlice_len _ _ _ $$ Hro
  ihave %Hswf := ownSlice_wf _ _ _ $$ Hro
  wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  ihave IH : iprop(∃ (k gi : w64), "i" ∷ i_ptr ↦ k ∗ "Hgi" ∷ gi_ptr ↦ gi ∗
      "Hro" ∷ sv.readonlyTXIDs' ↦* σ.readonly ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (σ.readonly.length : Int) ∧
        ∀ j < sint.nat k, σ.readonly[j]? ≠ some tid⌝) $$ [i Hgi Hro]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun j hj => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat k < σ.readonly.length := by word
    list_elem σ.readonly (sint.nat k) as e
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z k) σ.readonly _ e Hk.1 $$ [Hro] with Hro
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z k) σ.readonly _ e Hk.1 $$ [Hro] with Hro
    · iframe; ipureintro; exact He_lookup
    try wp_auto
    wp_if_destruct
    · have Hlast : σ.readonly.length - 1 < σ.readonly.length := by omega
      list_elem σ.readonly (σ.readonly.length - 1) as y
      have hli : sint.Z (sv.readonlyTXIDs'.len - W64 1) = (σ.readonly.length - 1 : Nat) := by word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_load_slice_index _ (sint.Z (sv.readonlyTXIDs'.len - W64 1)) σ.readonly _ y
        (by word) $$ [Hro] with Hro
      · iframe; ipureintro; rw [hli]; exact Hy_lookup
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
      wp_apply wp_store_slice_index _ (sint.Z k) σ.readonly y $$ [Hro] as Hro
      · iframe; ipureintro; exact ⟨Hk.1, by word⟩
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
      icases (ownSlice_split_all (sv.readonlyTXIDs'.len - W64 1) _ _ _
        ⟨by word, by word⟩).1 $$ Hro with ⟨Hro, Hro2⟩
      ihave Hro_cap := ownSlice_slice_absorb_capacity _ _ (W64 0) (sv.readonlyTXIDs'.len - W64 1)
        ⟨by decide, by word, by word⟩ $$ [Hro2 Hro_cap]
      · iframe
      try wp_auto
      wp_for_post
      try wp_auto
      have h : ((σ.readonly.set (sint.Z k).toNat y).take
          (sint.nat (sv.readonlyTXIDs'.len - W64 1))).Perm (σ.readonly.erase tid) := by
        rw [Hif] at He_lookup
        have h := swapRemove_perm He_lookup Hk.2.2
        have hy : σ.readonly.getD (σ.readonly.length - 1) 0 = y := by
          simp [List.getD_eq_getElem?_getD, Hy_lookup]
        rw [hy] at h
        rw [show sint.nat (sv.readonlyTXIDs'.len - W64 1) = σ.readonly.length - 1 by word]
        exact h
      iapply HΦ
      isplitr
      · ipureintro; exact h
      iexists _, c
      simp only [named]
      isplitl
      · iexists pp; iframe; ipureintro; exact Hiface
      · ipureintro; exact Hok
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
  · have Hnot : tid ∉ σ.readonly := by
      intro hm
      obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hm
      exact Hk.2.2 j (by word) (by rw [List.getElem?_eq_getElem hj, e])
    iapply HΦ
    isplitr
    · ipureintro; rw [List.erase_of_not_mem Hnot]
    iexists sv, c
    simp only [named]
    isplitl
    · iexists pp; iframe; ipureintro; exact Hiface
    · ipureintro; exact Hok

end proof

end bbolt
end EtcdGrove
end Perennial
