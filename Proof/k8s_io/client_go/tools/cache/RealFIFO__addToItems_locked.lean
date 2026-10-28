/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__addToItems_locked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__addToItems_locked

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

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

theorem RealFIFO.addToItems_locked.wp_proof
    (wp_keyOf : RealFIFO.keyOf.spec (GF := GF) (hG := hG)) :
    RealFIFO.addToItems_locked.spec (GF := GF) (hG := hG) := by
  intro f OK kf mp g lk t skip obj ty v sl vs
  wp_start as ⟨#Hkf, #Hkey, #Hkany, #Htr, #Hmp, #Hg, #Hgok, #Hcond, #HOK, %hobj, Hitems, Hsl, Hcap⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_keyOf f OK kf obj) $$ [$Hkf $Hkey $Hkany]
  · isplitr
    · ipureintro; exact Or.inl ⟨ty, v, hobj⟩
    iintro -; iexact HOK
  iintro %k %err %hk
  obtain rfl := hk ⟨ty, v, hobj⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := Delta) [Delta.mk t obj]
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
  (try wp_auto)
  wp_apply sync.Cond.wp_Broadcast $$ [$Hcond]
  (try wp_auto)
  cases g with
  | nil => iunfold gaugeOk at Hgok; icases Hgok with ⟨⟩
  | ok gi =>
    iunfold gaugeOk at Hgok
    (try wp_auto)
    wp_apply Hgok
    (try wp_auto)
    iapply HΦ
    iexists sl'
    iframe

end proof

end cache
end EtcdGrove
end Perennial
