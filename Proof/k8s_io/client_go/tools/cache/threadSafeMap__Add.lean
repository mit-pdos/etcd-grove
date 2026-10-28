/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__Add.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Add
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Update

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

theorem threadSafeMap.Add.wp_proof
    (wp_Update : threadSafeMap.Update.spec (GF := GF) (hG := hG)) :
    threadSafeMap.Add.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam D rvOf key obj
  iintro %Φ ⟨#Hpkg, #Hc, #Hacc, #HD, #HOK⟩ HAU
  wp_method_call
  wp_call
  wp_auto
  wp_bind
  iapply (wp_Update c γ OK Fam D rvOf key obj) $$ [$Hpkg $Hc $Hacc $HD $HOK]
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
