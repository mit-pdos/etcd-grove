/-
Lean-first (no Rocq counterpart).

More wrappers of `Set[T]`'s value methods in the `*Set[T]` method set, as `PtrMethods.lean`
(`UnsortedList`), for the proofs of batch 1 of the authorizer package.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]
variable {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
  {T : go.GoType} [IntoValTyped (GF := GF) K T]

/-- `(*Set[T]).UnsortedList` on the set `*l`. -/
theorem Set.wp_ptr_UnsortedList_of (wp_UnsortedList : Set.UnsortedList.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (m : Loc) (dq : DFrac) (s : GMap K Elem) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : Set'' K) ∗ m ↦${dq} s }}
      (App (Val (l @!! go.GoType.PointerType (Set''.ty T) @!! go!"UnsortedList")) (Val #()))
    {{ (sl : GoSlice) (ks : List K), RET #sl; l ↦{dl} (m : Set'' K) ∗ m ↦${dq} s ∗ sl ↦* ks ∗
        ⌜(∀ k, k ∈ ks ↔ (s !! k).isSome) ∧ ks.Nodup ∧ ks.length = GMap.size s⌝ }} := by
  wp_start as ⟨Hl, Hm⟩
  wp_auto
  wp_apply wp_UnsortedList (T := T) $$ [$Hm] as %sl %ks ⟨Hm, Hsl, %Hks⟩
  iapply HΦ; iframe
  ipureintro; exact Hks

end wps

end sets
end EtcdGrove
end Perennial
