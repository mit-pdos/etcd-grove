/-
`typed.TypedValue.Merge`: proved (Prove phase, 2026-11-20): the receiver's copy made persistent
(`isTV`), then `merge` with `ruleKeepRHS` (the package fact).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Merge
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.merge
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

theorem typed.TypedValue.Merge.wp_proof
    (h_merge : typed.merge.spec (GF := GF)) :
    typed.TypedValue.Merge.spec (GF := GF) := fun tv q sc S t l r => by
  wp_start as ⟨#Htv, #Hq⟩
  ihave #HP := typedPkgInit_poolsAt $$ Hpkg
  unfold typedPoolsAt
  icases HP with ⟨#Hr, #Hok, -⟩
  wp_auto
  ipersist tv
  ihave #Hl := (isTV_isTVv_law_holds tv_ptr sc S t l).mpr $$ []
  · iexists tv; iframe #
  wp_apply h_merge tv_ptr q sc S t l r typed.ruleKeepRHSV func.nil $$ [] as %p %err ⟨%He, Hp⟩
  · iframe #; ipureintro; rfl
  iapply HΦ
  iframe
  ipureintro; exact He

end proof

end smd
end EtcdGrove
end Perennial
