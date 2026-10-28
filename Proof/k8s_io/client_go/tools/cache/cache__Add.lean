/-
Proof of `Spec/k8s_io/client_go/tools/cache/cache__Add.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.cache__Add
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem cache.Add.wp_proof
    (wp_inner : threadSafeMap.Add.spec (GF := GF) (hG := hG)) :
    cache.Add.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf D KF rvOf obj
  iintro %Φ ⟨#Hpkg, #Hca, #Hkey, #Hacc, #HD, #HOK⟩ HAU
  iunfold isCache at Hca
  icases Hca with ⟨#Hcs, #Hkf, #Htr, #Hts⟩
  iunfold keyOk at Hkey
  wp_method_call
  wp_call
  wp_auto
  wp_apply Hkey $$ [$HD]
  iintro %k %err %hk
  obtain ⟨rfl, rfl⟩ := hk
  wp_auto
  wp_bind
  iapply (wp_inner ts γ OK Fam D rvOf (KF obj) obj) $$ [$Hpkg $Hts $Hacc $HD $HOK]
  inext
  imod HAU with ⟨%σ, Hst, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  imod Hcl $$ Hst with HK
  imodintro
  iintro -
  wp_auto
  iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
