/-
**Helpers of the validating, field-set and removing walkers' loop proofs** (part A2): appending
two empty error lists (`errs = append(errs, v2.validate(...)...)`).

Prove phase, round 2 (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

namespace LawA2

/-- A found entry is an entry. -/
theorem lookupKV_mem {α : Type} (k : GoString) (v : α) :
    ∀ (l : List (GoString × α)), lookupKV k l = some v → (k, v) ∈ l
  | [], h => by simp [lookupKV] at h
  | (k', v') :: rest, h => by
    simp only [lookupKV] at h
    split at h
    · cases h; subst_vars; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupKV_mem k v rest h)

/-- `append(errs, more...)` of two empty error lists is an empty error list. -/
theorem wp_append_noErrs (a b : GoSlice) :
    {{ noErrs (GF := GF) a ∗ noErrs b }}
      (App (App (Val #(functions go.append [typed.ValidationErrors.ty])) (Val #a)) (Val #b))
    {{ (r : GoSlice), RET #r; noErrs r }} := by
  iintro %Φ ⟨Ha, Hb⟩ HΦ
  iunfold noErrs at Ha
  iunfold ownErrs at Ha
  iunfold noErrs at Hb
  iunfold ownErrs at Hb
  icases Ha with ⟨Ha, Hac⟩
  icases Hb with ⟨Hb, -⟩
  wp_apply (wp_slice_append (V := typed.ValidationError) a [] b [] (DFrac.own 1))
    $$ [Ha Hac Hb] as %r ⟨Hr, Hrc, -⟩
  · iframe
  iapply HΦ
  unfold noErrs ownErrs
  iframe

end LawA2

end proof

end smd
end EtcdGrove
end Perennial
