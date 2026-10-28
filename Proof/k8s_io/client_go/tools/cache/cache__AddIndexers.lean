/-
Proof of `Spec/k8s_io/client_go/tools/cache/cache__AddIndexers.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.cache__AddIndexers

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

theorem cache.AddIndexers.wp_proof
    (wp_inner : threadSafeMap.AddIndexers.spec (GF := GF) (hG := hG)) :
    cache.AddIndexers.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf nm dn nfv nids hsz
  iintro %Φ ⟨#Hpkg, #Hca, Hnm, #Hfns⟩ HAU
  iunfold isCache at Hca
  icases Hca with ⟨#Hcs, #Hkf, #Htr, #Hts⟩
  wp_method_call
  wp_call
  wp_auto
  wp_bind
  iapply (wp_inner ts γ OK Fam nm dn nfv nids hsz) $$ [$Hpkg $Hts $Hnm $Hfns]
  inext
  imod HAU with ⟨%σ, Hst, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  iintro Hst
  imod Hcl $$ Hst with HK
  imodintro
  iintro %err Hpost
  wp_auto
  iapply HK; iexact Hpost

end proof

end cache
end EtcdGrove
end Perennial
