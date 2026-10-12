/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/adt/StringAffineComparable__Compare.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.StringAffineComparable__Compare

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

/-- A Go string's length (below `2^63`) as a word is zero only for the empty string. -/
theorem adt.w64_length_eq_zero {l : GoString} (h : l.length < 2 ^ 63) :
    W64 l.length = W64 0 ↔ l = [] := by
  constructor
  · intro h'
    have : l.length = 0 := by word
    exact List.eq_nil_of_length_eq_zero this
  · rintro rfl; rfl

theorem adt.StringAffineComparable.Compare.wp_proof :
    adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG) := by
  intro s s'
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hs
  wp_if_destruct
  · rw [adt.w64_length_eq_zero Hs] at Hif; subst Hif
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hs'
    wp_if_destruct
    · rw [adt.w64_length_eq_zero Hs'] at Hif; subst Hif
      rw [adt.affCmp_self]
      wp_end
    · rw [adt.w64_length_eq_zero Hs'] at Hif
      unfold adt.affCmp; simp only [Hif, ↓reduceIte]
      wp_end
  · rw [adt.w64_length_eq_zero Hs] at Hif
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hs'
    wp_if_destruct
    · rw [adt.w64_length_eq_zero Hs'] at Hif; subst Hif
      unfold adt.affCmp; simp only [Hif, ↓reduceIte]
      wp_end
    · rw [adt.w64_length_eq_zero Hs'] at Hif
      wp_if_destruct
      · unfold adt.affCmp; simp only [*, ↓reduceIte]
        wp_end
      · wp_if_destruct
        · unfold adt.affCmp; simp only [*, ↓reduceIte]
          wp_end
        · unfold adt.affCmp; simp only [*, ↓reduceIte]
          wp_end

end proof

end EtcdGrove
end Perennial
