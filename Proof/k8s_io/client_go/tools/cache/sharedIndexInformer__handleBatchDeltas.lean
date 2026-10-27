/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedIndexInformer__handleBatchDeltas.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__handleBatchDeltas

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

theorem sharedIndexInformer.handleBatchDeltas.wp_proof
    (wp_pDB : processDeltasInBatch.spec (GF := GF) (hG := hG)) :
    sharedIndexInformer.handleBatchDeltas.spec (GF := GF) (hG := hG) := by
  intro s lg ca ts γ OK Fam kf kf' KF rvOf SW Rw H BL ds vs sl b P Q hty
  wp_start as ⟨#Hidx, #Hkf, #Hca, Hr, #Hsw, %HRw, #Hmu, #Hh, Hfd, Hsl, %Hkind, #Hkey, #Hkey', #Hacc, HP,
    Hstep⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Lock (s.[sharedIndexInformer, go!"blockDeltas"])
    (blockDeltasRes SW H BL)) $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold blockDeltasRes at HR
  icases HR with ⟨%σ, %evs, HSW, HH, HBL⟩
  (try wp_auto)
  simp only [siiObj]
  wp_apply (wp_pDB lg _ ca ts γ OK Fam kf kf' KF rvOf (fun σ => iprop(SW σ ∗ P)) Rw σ H evs ds vs sl b hty)
    $$ [$Hpkg $Hca $Hr $Hsw $HSW $HP $Hh $HH $Hfd $Hsl $Hkey $Hkey' $Hacc]
    as ⟨%σ', %evs', %Hst, ⟨HSW, HP⟩, HH, Hsl, Hr⟩
  · ipureintro; exact ⟨HRw σ, Hkind⟩
  ihave HQ := Hstep $$ %σ %evs %σ' %evs' HP HSW HBL %Hst
  imod HQ with ⟨HSW, HBL, HQ⟩
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock (s.[sharedIndexInformer, go!"blockDeltas"])
    (blockDeltasRes SW H BL)) $$ [$Hmu $Hlocked HSW HH HBL]
  · iunfold blockDeltasRes; iexists σ', evs ++ evs'; iframe
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end cache
end EtcdGrove
end Perennial
