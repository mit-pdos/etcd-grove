module
public import Spec.go_etcd_io.bbolt.DB__getPageSizeFromFirstMeta
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__PageSize
public import Spec.os.File__ReadAt

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
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem DB.getPageSizeFromFirstMeta.wp_proof (hReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (hpib : DB.pageInBuffer.spec (GF := GF) (hG := hG))
    (hMeta : Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : Meta.Validate.spec (GF := GF) (hG := hG))
    (hPageSize : Meta.PageSize.spec (GF := GF) (hG := hG)) :
    DB.getPageSizeFromFirstMeta.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs ps dq
  wp_start as ⟨Hf, Hps, #Hof, Hfb⟩
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  icases bboltError_access errors.ErrInvalid (by simp [bboltErrorNames]) $$ Hei
    with ⟨%e, #He, %Hne⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, arrayIndexRef_zero,
    show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
  have hz : (zero_val (GoArray w8 4096)).arr = List.replicate 4096 (W8 0) := by
    first | rfl | simp [zero_val]
  ihave Hsl := slice_array buf_ptr 4096 (zero_val (GoArray w8 4096)) (by rw [hz, List.length_replicate]; omega) $$ buf
  rw [hz] at *
  wp_apply hReadAt f fd bs _ _ (W64 0) (by decide) $$ [Hof Hfb Hsl] as %n %err ⟨%k, %hk, Hfb, Hsl⟩
  · iframe; iframe #
  try wp_auto
  obtain ⟨hk1, rfl, hk3⟩ := hk
  obtain ⟨t', p', rfl⟩ := Hne
  cases err with
  | ok ei =>
    -- the read failed: an error
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    right
    exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | nil =>
    have hk4 : k = 4096 := by have := hk3 rfl; rw [List.length_replicate] at this; exact this
    subst hk4
    have hlen : 4096 ≤ bs.length := by
      rw [List.length_replicate, show sint.nat (W64 0) = 0 from rfl, List.drop_zero,
        List.length_take] at hk1
      omega
    try wp_auto
    rw [show sint.Z (W64 0) = 0 from rfl, arrayIndexRef_zero,
      show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
    have hne : List.take 4096 bs ≠ [] := List.ne_nil_of_length_pos (by rw [List.length_take]; omega)
    rw [List.drop_zero,
      List.drop_eq_nil_of_le (by rw [List.length_replicate]; exact Nat.le_refl _ : (List.replicate 4096 (W8 0)).length ≤ 4096),
      List.append_nil]
    icases (ownSlice_bytes _ _ _ hne).1 $$ Hsl with ⟨Hsl, %Hslen⟩
    icases persistent_entails_left (bytesPointsto_car buf_ptr _ _ hne) $$ Hsl
      with ⟨Hsl, %Hcar⟩
    wp_apply hpib dbl ps dq _ (W64 0) Hcar (by word) (by word) $$ [Hps] as Hps
    · iframe
    try wp_auto
    wp_apply hMeta _
    try wp_auto
    rw [show sint.Z (W64 0 * ps) = 0 by word]
    icases meta_in_bytes buf_ptr (DFrac.own 1) (List.take 4096 bs) 16 (by rw [List.length_take]; omega) Hcar $$ Hsl
      with ⟨HM, Hback⟩
    rw [show buf_ptr +ₗ 0 +ₗ 16 = buf_ptr +ₗ ((16 : Nat) : Int) by simp [Loc.add]]
    wp_apply hValidate _ _ _ (by simpa [Loc.add] using Hcar) $$ [HM] as %e1 ⟨HM, %He1⟩
    · iframe
    try wp_auto
    have hmeta : metaAt (List.take 4096 bs) 16 = metaAt bs 16 := by
      unfold metaAt; congr 1; rw [List.drop_take, List.take_take]; (try congr 1); (try omega)
    cases e1 with
    | nil =>
      -- valid: its page size
      try wp_auto
      wp_apply hPageSize _ _ _ $$ [HM] as HM
      · iframe
      try wp_auto
      iapply HΦ
      ihave Hsl := Hback $$ HM
      iframe
      ipureintro
      left
      refine ⟨rfl, rfl, hlen, (by rw [← hmeta]; exact He1.1.1 rfl), ?_⟩
      rw [← hmeta]
      word
    | ok ei =>
      -- invalid: an error
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      right
      exact ⟨fun h => (by cases h), fun _ => hlen⟩

end proof

end bbolt
end EtcdGrove
end Perennial
