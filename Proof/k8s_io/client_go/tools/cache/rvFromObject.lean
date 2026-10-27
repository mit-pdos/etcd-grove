/-
Proof of `Spec/k8s_io/client_go/tools/cache/rvFromObject.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.rvFromObject

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem rvFromObject.wp_proof : rvFromObject.spec (GF := GF) (hG := hG) := by
  intro OK rvOf o
  wp_start as ⟨#Hacc, #HOK⟩
  iunfold rvAcc at Hacc
  wp_auto
  wp_apply Hacc $$ [$HOK] as %m %err Hm
  cases hr : rvOf o with
  | none =>
    icases Hm with %herr
    (try wp_auto)
    cases err with
    | nil => exact absurd rfl herr
    | ok e =>
      (try wp_auto)
      iapply HΦ
      ipureintro; exact ⟨rfl, herr⟩
  | some r =>
    icases Hm with ⟨%herr, #Hget⟩
    subst herr
    wp_auto
    cases m with
    | nil => iunfold getRVOk at Hget; icases Hget with ⟨⟩
    | ok i =>
      iunfold getRVOk at Hget
      (try wp_auto)
      wp_apply Hget
      (try wp_auto)
      iapply HΦ
      ipureintro; exact ⟨rfl, rfl⟩

end proof

end cache
end EtcdGrove
end Perennial
