/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__Delete.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Delete
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__DeleteWithObject

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

theorem threadSafeMap.Delete.wp_proof
    (wp_DWO : threadSafeMap.DeleteWithObject.spec (GF := GF) (hG := hG)) :
    threadSafeMap.Delete.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam key
  iintro %Φ ⟨#Hpkg, #Hc⟩ HAU
  wp_method_call
  wp_call
  wp_auto
  wp_bind
  iapply (wp_DWO c γ OK Fam OK (fun _ => none) key GoInterface.nil) $$ [$Hpkg $Hc]
  · isplitr
    · iunfold okNil; ileft; ipureintro; rfl
    · imodintro; iintro %h; exact absurd rfl h
  inext
  imod HAU with ⟨%σ, Hst, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  have hr : rvOfObj (fun _ => none) GoInterface.nil = none := by simp [rvOfObj]
  rw [hr]
  imod Hcl $$ Hst with HK
  imodintro
  iintro -
  wp_auto
  iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
