/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__Get.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Get

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

theorem threadSafeMap.Get.wp_proof : threadSafeMap.Get.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam key
  iintro %Φ ⟨#Hpkg, #Hc, Hrd⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hc
  icases Hc with ⟨%mp, %g, #Hidx, #Him, #Hmp, #Hg, #Hgok, #Hguard⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  iunfold tsReader at Hrd
  wp_apply (lc := 2) sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  iunfold tsP at HP
  icases HP with ⟨%σ, %ph, Hst, Hgp, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrv, Hind, Hix, Hfv⟩
  wp_auto
  wp_apply (wp_map_lookup2 go.string (go.GoType.InterfaceType []) ph.il σ.items key)
    $$ [$Hil] as Hil
  imod storeSt_peek γ _ σ _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
  (try wp_auto)
  ihave #Hitem : okNil OK ((σ.items !! key).getD GoInterface.nil) $$ []
  · iunfold tsPers at Hpers
    icases Hpers with ⟨-, #Hits⟩
    cases hk : σ.items !! key with
    | none => iunfold okNil; ileft; ipureintro; rfl
    | some o => iapply BigSepM.bigSepM_lookup hk $$ Hits
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hgp Hitems Hrv Hind Hix Hfv Hil Hst]
  · inext
    iunfold tsP
    iexists σ, ph
    iframe; iframe #
    isplitl
    · iunfold tsPhys; iframe
    · ipureintro; exact Hok
  iintro Hrd
  wp_auto
  iapply HK
  iframe #
  isplitr
  · ipureintro; exact ⟨rfl, by simp [GMap.mem_iff]⟩
  iunfold tsReader; iexact Hrd

end proof

end cache
end EtcdGrove
end Perennial
