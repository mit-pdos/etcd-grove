/-
**Helpers of `value`'s comparison/equality recursion** (structured-merge-diff v7.0.0): a list
view's `RangeUsing` from the concrete specs of its two dynamic types (for `ListCompareUsing`, which
does not call `Length`). Defs-tier: imports specs, never proofs. Prove phase (2026-11-20).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing_ptr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

/-- A list view's `RangeUsing`, from the concrete specs of its two dynamic types. -/
theorem isListV_rangeDispatch
    (hR : value.listUnstructured.RangeUsing.spec (GF := GF))
    (hRP : value.listUnstructured.RangeUsing_ptr.spec (GF := GF))
    (l : value.List') (vs : List UVal) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV l vs ⊢
      ∃ i, ⌜l = .ok i⌝ ∗
        □ (∀ (a : value.Allocator), {{ isAlloc a }}
            (App (Val #(methods i.ty go!"RangeUsing" i.v)) (Val #a))
            {{ (r : value.ListRange), RET #r; isAlloc a ∗ ownRange r vs (-1) }}) := by
  iintro ⟨#Hpkg, #Hl⟩
  ihave %Hc := isListV_concrete_law_holds l vs $$ Hl
  rcases Hc with ⟨sl, rfl⟩ | ⟨p, rfl⟩
  · iexists _
    isplitr
    · ipureintro; rfl
    · imodintro
      iintro %a %Φ !> Ha HΦ
      iapply hR sl vs a $$ [Ha] [HΦ]
      · iframe; isplitr
        · iexact Hpkg
        · iexact Hl
      · iexact HΦ
  · iexists _
    isplitr
    · ipureintro; rfl
    · imodintro
      iintro %a %Φ !> Ha HΦ
      iapply hRP p vs a $$ [Ha] [HΦ]
      · iframe; isplitr
        · iexact Hpkg
        · iexact Hl
      · iexact HΦ

end lemmas

end smd
end EtcdGrove
end Perennial
