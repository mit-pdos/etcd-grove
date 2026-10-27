/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__Delete.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__Delete
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__checkSynced_locked
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem RealFIFO.Delete.wp_proof
    (wp_check : RealFIFO.checkSynced_locked.spec (GF := GF) (hG := hG))
    (wp_add : RealFIFO.addToItems_locked.spec (GF := GF) (hG := hG)) :
    RealFIFO.Delete.spec (GF := GF) (hG := hG) := by
  intro f γ OK KF obj ty v
  iintro %Φ ⟨#Hpkg, #Hf, #HOK, %hobj⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isFIFO at Hf
  icases Hf with ⟨%ch, %kf, %mp, %g, %h, %uwp, %idn, #Hkf, #Hkey, #Htr, #Hae, #Hbm, #Huwp, #Hbs,
    #Hch, #Hmp, #Hg, #Hgok, #Hh, #Hhok, #Hguard, #Hcond, #Hinv, #Hid, #Hkany⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (lc := 3) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, Htok⟩
  imod fifo_acquire f γ OK ch $$ Hinv Hlc1 Hlc2 Htok with HR
  iunfold fifoRes at HR
  icases HR with ⟨%q, %sl, %vs, Hex, Hst, Hsy, Hitems, Hsl, Hcap, Hds, Hpop, Hinit, %Hic,
    Hsc, Hcl, Hbc⟩
  imod fifoSt_update_sy γ q (FQ.addObj go!"Deleted" obj)
    (fun h => by show (q.synced || _) = true; rw [h]) _ $$ [$Hst $Hsy $HAU] with ⟨Hst, Hsy, Hlb, HK⟩
  (try wp_auto)
  wp_apply (wp_check f ch γ.ch (fifoSyncedLb γ) true q.initCount q.synced)
    $$ [$Hpop $Hinit $Hsc $Hch $Hbc Hlb] as ⟨Hpop, Hinit, Hsc, Hbc⟩
  · isplitr
    · ipureintro; exact Hic
    iintro %hs
    have : (FQ.addObj go!"Deleted" obj q).synced = true := by
      simp only [syncsNow, Bool.true_and, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
      simp [FQ.addObj, hs.1]
    rw [this]; simp only [↓reduceIte]
    icases Hlb with #Hlb
    imodintro; iexact Hlb
  have hsy : (q.synced || syncsNow true q.initCount q.synced) =
      (FQ.addObj go!"Deleted" obj q).synced := by
    simp only [FQ.addObj, syncsNow]; cases q.synced <;> simp
  rw [hsy]
  (try wp_auto)
  wp_apply (wp_add f OK KF kf mp g _ go!"Deleted" false obj ty v sl vs)
    $$ [$Hpkg $Hkf $Hkey $Hkany $Htr $Hmp $Hg $Hgok $Hcond $HOK $Hitems $Hsl $Hcap]
    as ⟨%sl', Hitems, Hsl, Hcap⟩
  · ipureintro; exact hobj
  ihave Hds := fifo_push OK q.items vs (.obj go!"Deleted" obj) _ $$ [$Hds]
  · iunfold fdAt; dsimp only; iframe #; ipureintro; exact ⟨rfl, ty, v, hobj⟩
  (try wp_auto)
  imod fifo_release f γ OK ch $$ Hinv Hlc3 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
    with Htok
  · iunfold fifoRes
    iexists (FQ.addObj go!"Deleted" obj q), sl', _
    simp only [FQ.addObj]
    iframe
    ipureintro; exact Hic
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
  (try wp_auto)
  iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
