/-
`value.mapUnstructuredString.Iterate`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__IterateUsing
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

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

theorem value.mapUnstructuredString.Iterate.wp_proof
    (h_mapUnstructuredString_IterateUsing : value.mapUnstructuredString.IterateUsing.spec (GF := GF)) :
    value.mapUnstructuredString.Iterate.spec (GF := GF) := fun m kvs fn I Q => by
  wp_start as ⟨Hm, #Hfn, HI⟩
  icases valuePkg_globals $$ Hpkg with ⟨%ha, %er, #Hha, -⟩
  wp_auto
  wp_method_call
  wp_auto
  wp_apply h_mapUnstructuredString_IterateUsing m kvs _ fn I Q $$ [Hm HI] as %r ⟨-, Hr⟩
  · iframe
    isplitr
    · iapply isAlloc_heap_intro
    iunfold iterFnOk at Hfn
    iunfold iterUFnOk
    imodintro
    iintro %done %k %x %v %Hst %Φ' !> ⟨Ha, HI, Hv⟩ HΦ'
    iapply Hfn $$ %done %k %x %v %Hst [HI Hv]
    · iframe
    inext
    iintro %b Hb
    iapply HΦ'
    iframe
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
