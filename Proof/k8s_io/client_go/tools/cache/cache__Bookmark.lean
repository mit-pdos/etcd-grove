/-
Proof of `Spec/k8s_io/client_go/tools/cache/cache__Bookmark.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.cache__Bookmark
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Bookmark

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

theorem cache.Bookmark.wp_proof
    (wp_inner : threadSafeMap.Bookmark.spec (GF := GF) (hG := hG)) :
    cache.Bookmark.spec (GF := GF) (hG := hG) := by
  intro ca ts γ OK Fam kf rv
  iintro %Φ ⟨#Hpkg, #Hca⟩ HAU
  iunfold isCache at Hca
  icases Hca with ⟨#Hcs, #Hkf, #Htr, #Hts⟩
  wp_method_call
  wp_call
  wp_auto
  wp_bind
  iapply (wp_inner ts γ OK Fam rv) $$ [$Hpkg $Hts]
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
