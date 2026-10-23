/-
`BytesAffineComparable.Compare`'s proof (the auth plan's S2, 2026-10-23): the empty-slice cases
by the slices' lengths, the rest `bytes.Compare` (Perennial's, `bytes.wp_Compare`), whose
three-way result is `affCmp`'s by the string order's trichotomy.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.BytesAffineComparable__Compare
public import Proof.go_etcd_io.etcd.pkg.v3.adt.BytesIvl
public import Perennial.Proof.bytes.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `bytes.Compare`'s result is `affCmp`'s on non-empty strings. -/
theorem adt.compareResult_eq_affCmp (a b : GoString) (ha : a ≠ []) (hb : b ≠ []) :
    bytes.compareResult a b = W64 (adt.affCmp a b) := by
  unfold bytes.compareResult adt.affCmp
  simp only [ha, hb, ↓reduceIte]
  by_cases h1 : go.GoStringLt a b
  · simp only [h1, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : go.GoStringLt b a
    · have hne : a ≠ b := by rintro rfl; exact go.goStringLt_irrefl _ h2
      simp only [h2, hne, ↓reduceIte]
    · have heq : a = b := go.goStringLt_eq_of_not_lt h1 h2
      subst heq
      simp [go.goStringLt_irrefl]

theorem adt.BytesAffineComparable.Compare.wp_proof :
    adt.BytesAffineComparable.Compare.spec (GF := GF) (hG := hG) := by
  intro s s' bs bs' d d'
  wp_start as ⟨Hs, Hs'⟩
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  ihave %Hl' := ownSlice_len _ _ _ $$ Hs'
  have h0 := adt.slice_len_eq_zero Hl
  have h0' := adt.slice_len_eq_zero Hl'
  wp_auto
  wp_if_destruct
  · rw [h0] at Hif; subst Hif
    wp_if_destruct
    · rw [h0'] at Hif; subst Hif
      rw [adt.affCmp_self]
      wp_end
    · rw [h0'] at Hif
      unfold adt.affCmp; simp only [Hif, ↓reduceIte]
      wp_end
  · rw [h0] at Hif
    wp_if_destruct
    · rw [h0'] at Hif; subst Hif
      unfold adt.affCmp; simp only [Hif, ↓reduceIte]
      wp_end
    · rw [h0'] at Hif
      rename_i Hne
      wp_apply bytes.wp_Compare $$ [$Hs $Hs'] as ⟨Hs, Hs'⟩
      rw [adt.compareResult_eq_affCmp bs bs' Hne Hif]
      wp_end

end proof

end EtcdGrove
end Perennial
