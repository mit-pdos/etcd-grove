/- Lean-first (no Rocq counterpart). The proof of `inRange`: its three cases. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- Go's `<=` on strings is the negation of the converse `<` (a fact about Perennial's
`GoStringLe`, to move to Perennial: `notes/perennial-changes.md`). -/
theorem goStringLe_iff_not_lt (a b : GoString) : go.GoStringLe a b ↔ ¬ go.GoStringLt b a := by
  constructor
  · rintro (rfl | h)
    · exact go.goStringLt_irrefl a
    · exact go.goStringLt_asymm h
  · intro h
    by_cases h' : go.GoStringLt a b
    · exact Or.inr h'
    · exact Or.inl (go.goStringLt_eq_of_not_lt h' h)

theorem inRange.wp_proof : inRange.spec (GF := GF) (hG := hG) := by
  intro key endk kk e k dq dq'
  wp_start as ⟨Hk, He⟩
  wp_auto
  ihave %Hel := ownSlice_len $$ He
  wp_if_destruct
  · simp only [inRangeM, ↓reduceIte]
    wp_apply wp_bytes_to_string key kk dq $$ [$Hk] as Hk
    (try wp_auto)
    iapply HΦ; iframe
  · simp only [inRangeM, Bool.false_eq_true, ↓reduceIte, mvcc.inRange]
    wp_if_destruct
    · have he : e = [] := List.eq_nil_of_length_eq_zero (by rw [Hel.1, Hif]; rfl)
      wp_apply wp_bytes_to_string key kk dq $$ [$Hk] as Hk
      (try wp_auto)
      simp only [he, decide_true, Bool.true_or, Bool.and_true]
      rw [show decide (go.GoStringLe kk k) = !decide (go.GoStringLt k kk) by
        rw [Bool.eq_iff_iff]; simp [goStringLe_iff_not_lt]]
      iapply HΦ; iframe
    · have he : e ≠ [] := by
        intro he; subst he; apply Hif; simp at Hel; word
      wp_apply wp_bytes_to_string key kk dq $$ [$Hk] as Hk
      (try wp_auto)
      simp only [decide_eq_false he, Bool.false_or]
      wp_if_destruct
      · wp_apply wp_bytes_to_string endk e dq' $$ [$He] as He
        (try wp_auto)
        rw [show (!decide (go.GoStringLt k kk)) = true by
          simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact (goStringLe_iff_not_lt _ _).1 Hif]
        iapply HΦ; iframe
      · (try wp_auto)
        rw [show (!decide (go.GoStringLt k kk)) = false by
          simp only [Bool.not_eq_false', decide_eq_true_eq]
          exact Classical.byContradiction fun h => Hif ((goStringLe_iff_not_lt _ _).2 h)]
        iapply HΦ; iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
