module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getField

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem getField.wp_proof : getField.spec (GF := GF) (hG := hG) := by
  intro sl dq d i hi0 hil
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  (try wp_auto)
  have hlen : (d.length : Int) = sint.Z sl.len := by rw [Hl.1]; word
  have hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
  wp_if_destruct
  · -- no length byte
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : getFieldD d (sint.nat i) = none := by
      unfold getFieldD; rw [if_pos (by word)]
    rw [this]
  have hlt : sint.nat i < d.length := by word
  have hget : d[(sint.Z i).toNat]? = some (d.getD (sint.nat i) (W8 0)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl
  rw [if_pos (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len by word)]
  wp_apply wp_load_slice_index sl (sint.Z i) d dq _ (by word) $$ [Hs] as Hs
  · iframe Hs; ipureintro; exact hget
  (try wp_auto)
  have hna : (uint.Z (d.getD (sint.nat i) (W8 0))) = ((d.getD (sint.nat i) (W8 0)).toNat : Int) :=
    rfl
  have hnb : (d.getD (sint.nat i) (W8 0)).toNat < 256 := (d.getD (sint.nat i) (W8 0)).isLt
  have hhi : sint.Z (i + W64 1 + W64 (uint.Z (d.getD (sint.nat i) (W8 0)))) =
      sint.Z i + 1 + (d.getD (sint.nat i) (W8 0)).toNat := by
    rw [hna]; word
  wp_if_destruct
  · -- the field runs past the data
    (try wp_auto)
    iapply HΦ
    iframe Hs
    ipureintro
    have : getFieldD d (sint.nat i) = none := by
      unfold getFieldD
      rw [if_neg (by word)]
      dsimp only
      rw [if_pos (by word)]
    rw [this]
  have hge : sint.nat i + 1 + (d.getD (sint.nat i) (W8 0)).toNat ≤ d.length := by word
  rw [if_pos (show 0 ≤ sint.Z (i + W64 1) ∧
      sint.Z (i + W64 1) ≤ sint.Z (i + W64 1 + W64 (uint.Z (d.getD (sint.nat i) (W8 0)))) ∧
      sint.Z (i + W64 1 + W64 (uint.Z (d.getD (sint.nat i) (W8 0)))) ≤ sint.Z sl.cap by
    rw [hhi, hi1]; omega)]
  icases (ownSlice_slice (i + W64 1) (i + W64 1 + W64 (uint.Z (d.getD (sint.nat i) (W8 0)))) sl dq d
    (by rw [hhi, hi1]; omega)).1 $$ Hs with ⟨A, B, C⟩
  wp_apply wp_bytes_to_string _ _ dq $$ [B] as B
  · iexact B
  ihave Hs := (ownSlice_slice (i + W64 1) (i + W64 1 + W64 (uint.Z (d.getD (sint.nat i) (W8 0))))
    sl dq d (by rw [hhi, hi1]; omega)).2 $$ [A B C]
  · iframe A B C
  (try wp_auto)
  iapply HΦ
  iframe Hs
  ipureintro
  have hdec : getFieldD d (sint.nat i) = some ((d.drop (sint.nat i + 1)).take
      (d.getD (sint.nat i) (W8 0)).toNat, sint.nat i + 1 + (d.getD (sint.nat i) (W8 0)).toNat) := by
    unfold getFieldD
    rw [if_neg (by omega)]
    dsimp only
    rw [if_neg (by omega)]
  rw [hdec]
  refine ⟨rfl, ?_, ?_⟩
  · unfold subslice
    have h1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have h2 : sint.nat (i + W64 1 + W64 (uint.Z (d.getD (sint.nat i) (W8 0)))) =
        sint.nat i + 1 + (d.getD (sint.nat i) (W8 0)).toNat := by have := hhi; word
    rw [h1, h2, List.drop_take]; congr 1; omega
  · rw [hhi]; word

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
