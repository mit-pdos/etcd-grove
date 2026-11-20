/-
`value.mapUnstructuredString.ZipUsing`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__ZipUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.defaultMapZip
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

theorem value.mapUnstructuredString.ZipUsing.wp_proof
    (h_defaultMapZip : value.defaultMapZip.spec (GF := GF)) :
    value.mapUnstructuredString.ZipUsing.spec (GF := GF) := fun m kvs al o or_ order fn I Q => by
  wp_start as ⟨Hm, Ho, Ha, %Hord, %Hzl, #Hfn, HI⟩
  wp_auto
  wp_apply h_defaultMapZip al _ o (some kvs) or_ order fn I Q $$ [Hm Ho Ha HI] as %b Hb
  · iframe
    isplitl [Hm]
    · simp only [isMapO]; iexact Hm
    isplitr
    · ipureintro; exact Hord
    isplitr
    · ipureintro; exact Hzl
    iexact Hfn
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
