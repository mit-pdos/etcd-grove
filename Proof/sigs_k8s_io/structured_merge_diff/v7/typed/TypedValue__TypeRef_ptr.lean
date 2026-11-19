/-
`typed.TypedValue.TypeRef_ptr`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__TypeRef_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__TypeRef

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA

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
variable [package_sem : typed.Assumptions]

theorem typed.TypedValue.TypeRef_ptr.wp_proof
    (h_TypedValue_TypeRef : typed.TypedValue.TypeRef.spec (GF := GF)) :
    typed.TypedValue.TypeRef_ptr.spec (GF := GF) := fun p sc S t x => by
  wp_start as Htv
  ihave H2 := (isTV_isTVv_law_holds p sc S t x).mp $$ Htv
  icases H2 with ⟨%tv, #Hp, #Htv⟩
  wp_auto
  wp_apply h_TypedValue_TypeRef tv
  unfold isTVv
  icases Htv with ⟨-, -, #Htr, -⟩
  iapply HΦ
  iexact Htr

end proof

end smd
end EtcdGrove
end Perennial
