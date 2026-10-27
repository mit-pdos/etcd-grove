/-
Proof of `Spec/k8s_io/client_go/tools/cache/cache__Get.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.cache__Get
public import Spec.k8s_io.client_go.tools.cache.cache__GetByKey

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

theorem cache.Get.wp_proof
    (wp_GetByKey : cache.GetByKey.spec (GF := GF) (hG := hG)) :
    cache.Get.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf D KF obj
  iintro %Φ ⟨#Hpkg, #Hca, #Hkey, #HD, Hr⟩ HAU
  ihave #Hca' := Hca
  iunfold isCache at Hca'
  icases Hca' with ⟨#Hcs, #Hkf, #Htr, #Hts⟩
  iunfold keyOk at Hkey
  wp_method_call
  wp_call
  wp_auto
  wp_apply Hkey $$ [$HD]
  iintro %k %err %hk
  obtain ⟨rfl, rfl⟩ := hk
  wp_auto
  wp_bind
  iapply (wp_GetByKey ca ts γ OK Fam kf (KF obj)) $$ [$Hpkg $Hca $Hr]
  inext
  imod HAU with ⟨%σ, Hst, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  imod Hcl $$ Hst with HK
  imodintro
  iintro %item %ok Hpost
  wp_auto
  iapply HK; iexact Hpost

end proof

end cache
end EtcdGrove
end Perennial
