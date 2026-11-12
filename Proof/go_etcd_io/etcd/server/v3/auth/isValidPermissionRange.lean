/-
`isValidPermissionRange`'s proof (the auth plan's S2, 2026-10-23); see `InvAuth.lean`, `PermTree.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.isValidPermissionRange
public import Spec.go_etcd_io.etcd.server.v3.auth.isOpenEnded
public import Spec.go_etcd_io.etcd.pkg.v3.adt.BytesAffineComparable__Compare
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.isValidPermissionRange.wp_proof
    (h_isOpenEnded : auth.isOpenEnded.spec (GF := GF) (hG := hG))
    (h_Compare : adt.BytesAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    auth.isValidPermissionRange.spec (GF := GF) (hG := hG) := by
  intro key re k e dk de
  wp_start as ⟨Hk, He⟩
  ihave #Hadt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt $$ []
  · iPkgInit
  ihave %Hlk := ownSlice_len _ _ _ $$ Hk
  ihave %Hle := ownSlice_len _ _ _ $$ He
  have hk0 := adt.slice_len_eq_zero Hlk
  have he0 := adt.slice_len_eq_zero Hle
  wp_auto
  wp_if_destruct
  · -- an empty key
    rw [hk0] at Hif
    iapply HΦ; iframe Hk He; ipureintro
    unfold rangeValid; simp [Hif]
  · rw [hk0] at Hif
    wp_if_destruct
    · -- a point
      rw [he0] at Hif
      rename_i Hkne
      iapply HΦ; iframe Hk He; ipureintro
      unfold rangeValid; simp [Hif, Hkne]
    · rw [he0] at Hif
      rename_i Hkne
      (try wp_auto)
      -- `begin.Compare(end)`: the value method through the variable's pointer
      rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.BytesAffineComparable.ty)
        (m := go!"Compare")]
      (try wp_auto)
      wp_apply (h_Compare key re k e dk de) $$ [$Hk $He] as ⟨Hk, He⟩
      have hb := adt.affCmp_bounds k e
      wp_if_destruct
      · -- `key < rangeEnd`
        rename_i Hene
        have hlt : adt.affCmp k e < 0 := by
          have : sint.Z (W64 (adt.affCmp k e)) = sint.Z (W64 (-1 : Int)) := by rw [Hif]
          word
        obtain ⟨-, hlt⟩ := (adt.affCmp_neg_iff k e).1 hlt
        rcases hlt with h | h
        · exact absurd h Hene
        iapply HΦ; iframe Hk He; ipureintro
        unfold rangeValid; simp [Hkne, h]
      · rename_i Hene
        have hnlt : ¬ go.GoStringLt k e := by
          intro h
          apply Hif
          have := (adt.affCmp_neg_iff k e).2 ⟨Hkne, Or.inr h⟩
          have : adt.affCmp k e = -1 := by omega
          rw [this]
        wp_apply (h_isOpenEnded re e de) $$ [$He] as He
        iapply HΦ; iframe Hk He; ipureintro
        unfold rangeValid
        rw [decide_eq_true_iff]
        simp [Hkne, Hene, hnlt]

end proof

end EtcdGrove
end Perennial
