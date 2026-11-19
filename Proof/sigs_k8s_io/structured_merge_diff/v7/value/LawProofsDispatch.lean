/-
**`value`'s interface dispatch from the concrete specs** (structured-merge-diff v7.0.0): an
allocator `isAlloc (.ok i)` has the triples of `allocIfaceM i`, given the concrete methods' specs
of its two dynamic types (as hypotheses: this defs-tier module imports their specs, never their
proofs). The proofs of `value`'s functions that call an `Allocator`'s methods use it, so that one
proof covers both dynamic types. Prove phase (2026-11-19).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsFreelist
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__allocListUnstructuredRange
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__allocListUnstructuredRange

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

/-- `Free` of an allocator, from the two concrete specs. -/
theorem isAlloc_Free
    (hHF : value.heapAllocator.Free.spec (GF := GF))
    (hFF : value.freelistAllocator.Free.spec (GF := GF)) (a : value.Allocator) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc a ⊢
      isAlloc a ∗ ∃ i, ⌜a = .ok i⌝ ∗ □ (∀ x : GoInterface, {{ isAlloc (.ok i) ∗ freeable x }}
        (App (Val #(methods i.ty go!"Free" i.v)) (Val #x))
        {{ RET #(); isAlloc (.ok i) }}) := by
  iintro ⟨#Hpkg, Ha⟩
  icases isAlloc_concrete_law_holds a $$ Ha with ⟨Ha, (⟨%p, %rfl⟩ | ⟨%p, %rfl⟩)⟩
  · iframe
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %x %Φ !> ⟨Ha, -⟩ HΦ
    iapply hHF p x $$ [] [HΦ Ha]
    · iexact Hpkg
    · inext; iintro -; iapply HΦ; iexact Ha
  · iframe
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %x %Φ !> Hpre HΦ
    iapply hFF p x $$ [Hpre] [HΦ]
    · iframe; iexact Hpkg
    · iexact HΦ

/-- `allocValueUnstructured` of an allocator, from the two concrete specs. -/
theorem isAlloc_allocV
    (hHV : value.heapAllocator.allocValueUnstructured.spec (GF := GF))
    (hFV : value.freelistAllocator.allocValueUnstructured.spec (GF := GF)) (a : value.Allocator) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc a ⊢
      isAlloc a ∗ ∃ i, ⌜a = .ok i⌝ ∗ □ ({{ isAlloc (.ok i) }}
        (App (Val #(methods i.ty go!"allocValueUnstructured" i.v)) (Val #()))
        {{ (q : Loc), RET #q; isAlloc (.ok i) ∗ wrapperOwn q }}) := by
  iintro ⟨#Hpkg, Ha⟩
  icases isAlloc_concrete_law_holds a $$ Ha with ⟨Ha, (⟨%p, %rfl⟩ | ⟨%p, %rfl⟩)⟩
  · iframe
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %Φ !> Ha HΦ
    iapply hHV p $$ [] [HΦ Ha]
    · iexact Hpkg
    · inext; iintro %q Hq; iapply HΦ; iframe
  · iframe
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %Φ !> Ha HΦ
    iapply hFV p $$ [Ha] [HΦ]
    · iframe; iexact Hpkg
    · iexact HΦ

/-- `allocListUnstructuredRange` of an allocator, from the two concrete specs. -/
theorem isAlloc_allocR
    (hHR : value.heapAllocator.allocListUnstructuredRange.spec (GF := GF))
    (hFR : value.freelistAllocator.allocListUnstructuredRange.spec (GF := GF)) (a : value.Allocator) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc a ⊢
      isAlloc a ∗ ∃ i, ⌜a = .ok i⌝ ∗ □ ({{ isAlloc (.ok i) }}
        (App (Val #(methods i.ty go!"allocListUnstructuredRange" i.v)) (Val #()))
        {{ (q : Loc), RET #q; isAlloc (.ok i) ∗ rangeOwn q }}) := by
  iintro ⟨#Hpkg, Ha⟩
  icases isAlloc_concrete_law_holds a $$ Ha with ⟨Ha, (⟨%p, %rfl⟩ | ⟨%p, %rfl⟩)⟩
  · iframe
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %Φ !> Ha HΦ
    iapply hHR p $$ [] [HΦ Ha]
    · iexact Hpkg
    · inext; iintro %q Hq; iapply HΦ; iframe
  · iframe
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %Φ !> Ha HΦ
    iapply hFR p $$ [Ha] [HΦ]
    · iframe; iexact Hpkg
    · iexact HΦ

end lemmas

end smd
end EtcdGrove
end Perennial
