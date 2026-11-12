/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedIndexInformer__handleDeltas.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__handleDeltas

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

theorem sharedIndexInformer.handleDeltas.wp_proof
    (wp_pD : processDeltas.spec (GF := GF) (hG := hG)) :
    sharedIndexInformer.handleDeltas.spec (GF := GF) (hG := hG) := by
  intro s lg ca ts γ OK Fam kf kf' KF rvOf SW Rw H BL d v sl b P Q
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
  wp_apply (wp_pD lg _ ca ts γ OK Fam kf kf' KF rvOf (fun σ => iprop(SW σ ∗ P)) Rw σ H evs d v sl b)
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
