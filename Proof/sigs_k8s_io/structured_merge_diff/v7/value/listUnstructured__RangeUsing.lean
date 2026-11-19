/-
`value.listUnstructured.RangeUsing`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__RangeUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__allocListUnstructuredRange
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__allocListUnstructuredRange
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.listUnstructured.RangeUsing.wp_proof
    (h_heapAllocator_allocListUnstructuredRange : value.heapAllocator.allocListUnstructuredRange.spec (GF := GF))
    (h_freelistAllocator_allocListUnstructuredRange : value.freelistAllocator.allocListUnstructuredRange.spec (GF := GF)) :
    value.listUnstructured.RangeUsing.spec (GF := GF) := fun l vs al => by
  wp_start as ⟨#Hl, Ha⟩
  icases isListV_val $$ Hl with ⟨%xs, #Hs, HL⟩
  ihave %Hlen := isIfaceL_length $$ HL
  ihave %Hsl := ownSlice_len $$ Hs
  ihave #Hli := isListV_iface $$ Hl
  icases valuePkg_globals $$ Hpkg with ⟨%ha, %er, -, #Her⟩
  wp_auto
  wp_if_destruct
  · have hvs : vs = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    subst hvs
    iapply HΦ
    iframe
    iunfold ownRange
    ileft
    iexists er
    ipureintro
    exact ⟨rfl, rfl, by omega⟩
  · icases isAlloc_concrete_law_holds al $$ Ha with ⟨Ha, (⟨%p, %rfl⟩ | ⟨%p, %rfl⟩)⟩
    · wp_auto
      wp_apply h_heapAllocator_allocListUnstructuredRange p as %q Hq
      iunfold rangeOwn at Hq
      icases Hq with ⟨%r, Hq, Hw⟩
      wp_auto
      iapply HΦ
      iframe
      iapply ownRange_intro q l r.vv' (W64 (-1)) vs (-1) (by decide)
      iframe
      iexact Hli
    · wp_auto
      wp_apply h_freelistAllocator_allocListUnstructuredRange p $$ [Ha] as %q ⟨Ha, Hq⟩
      · iexact Ha
      iunfold rangeOwn at Hq
      icases Hq with ⟨%r, Hq, Hw⟩
      wp_auto
      iapply HΦ
      iframe
      iapply ownRange_intro q l r.vv' (W64 (-1)) vs (-1) (by decide)
      iframe
      iexact Hli

end proof

end smd
end EtcdGrove
end Perennial
