/-
**A list's `Length` through `value.List`'s interface** (the merging and compare walkers' `doList`):
from the two concrete specs (`listUnstructured`, by value and by pointer), as `value`'s
`isAlloc_Free` does for `Free`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Empty

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

/-- `Length` of a list view, from the two concrete specs. -/
theorem isListV_Length
    (hL : value.listUnstructured.Length.spec (GF := GF))
    (hLp : value.listUnstructured.Length_ptr.spec (GF := GF)) (l : value.List') (vs : List UVal) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV l vs ⊢
      ∃ i, ⌜l = .ok i⌝ ∗ □ ({{ isListV (.ok i) vs }}
        (App (Val #(methods i.ty go!"Length" i.v)) (Val #()))
        {{ (r : w64), RET #r; ⌜r.toInt = vs.length⌝ }}) := by
  iintro ⟨#Hpkg, Hl⟩
  icases isListV_concrete_law_holds l vs $$ Hl with (⟨%sl, %rfl⟩ | ⟨%p, %rfl⟩)
  · iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %Φ !> Hpre HΦ
    iapply hL sl vs $$ [Hpre] [HΦ]
    · iframe; iexact Hpkg
    · iexact HΦ
  · iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %Φ !> Hpre HΦ
    iapply hLp p vs $$ [Hpre] [HΦ]
    · iframe; iexact Hpkg
    · iexact HΦ

/-- `Empty` of a map view, from the concrete spec (`mapUnstructuredString`, the only kind). -/
theorem isMapV_Empty
    (hE : value.mapUnstructuredString.Empty.spec (GF := GF)) (m : value.Map)
    (kvs : List (GoString × UVal)) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isMapV m kvs ⊢
      ∃ i, ⌜m = .ok i⌝ ∗ □ ({{ isMapV (.ok i) kvs }}
        (App (Val #(methods i.ty go!"Empty" i.v)) (Val #()))
        {{ (r : Bool), RET #r; ⌜r = true ↔ kvs = []⌝ }}) := by
  iintro ⟨#Hpkg, Hm⟩
  icases isMapV_concrete_law_holds m kvs $$ Hm with ⟨%gm, %rfl⟩
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ !> Hpre HΦ
  iapply hE gm kvs $$ [Hpre] [HΦ]
  · iframe; iexact Hpkg
  · iexact HΦ

end lemmas

end smd
end EtcdGrove
end Perennial
