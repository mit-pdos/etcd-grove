/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/sets/List.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.List
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Perennial.Spec.slices.Sort
public import Perennial.Spec.cmp.Less
public import Perennial.Proof.slices.OrderedBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem List'.wp_proof (wp_UnsortedList : Set.UnsortedList.spec (GF := GF) (hG := hG))
    (wp_Sort : _root_.Perennial.slices.Sort.spec (GF := GF) (hG := hG))
    (wp_Less : _root_.Perennial.cmp.Less.spec (GF := GF) (hG := hG)) :
    List'.spec (GF := GF) (hG := hG) := by
  intro m dq s hsz
  wp_start as Hm
  ihave #Hsl : isPkgInit (PROP := IProp GF) pkg_id.slices $$ []
  · iPkgInit
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_UnsortedList (T := go.string) $$ [$Hm] as %sl %ks ⟨Hm, Hks, %Hk⟩
  (try wp_auto)
  ihave #Hless := _root_.Perennial.slices.lessImplements_string_of (GF := GF) wp_Less
  wp_apply wp_Sort go.GoStringLt sl ks _root_.Perennial.slices.StrictWeakOrder_goStringLt $$ [Hks]
    with %ks' ⟨Hks, %Hperm, %Hsorted⟩
  · iframe Hks; iframe #; ipureintro; rw [Hk.2.2]; exact hsz
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro
  refine ⟨fun k => ?_, Hperm.nodup_iff.1 Hk.2.1, Hsorted⟩
  rw [← Hk.1 k]; exact Hperm.mem_iff.symm

end proof

end sets
end EtcdGrove
end Perennial
