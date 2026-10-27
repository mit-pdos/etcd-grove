/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__Update.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Update
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__updateLocked
public import Spec.k8s_io.client_go.tools.cache.rvFromObject
public import Spec.k8s_io.client_go.tools.cache.parseRVForMetricsWithTruncation

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

theorem threadSafeMap.Update.wp_proof
    (wp_rv : rvFromObject.spec (GF := GF) (hG := hG))
    (wp_parse : parseRVForMetricsWithTruncation.spec (GF := GF) (hG := hG))
    (wp_upd : threadSafeMap.updateLocked.spec (GF := GF) (hG := hG)) :
    threadSafeMap.Update.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam D rvOf key obj
  iintro %Φ ⟨#Hpkg, #Hc, #Hacc, #HD, #HOK⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hc
  icases Hc with ⟨%mp, %g, #Hidx, #Him, #Hmp, #Hg, #Hgok, #Hguard⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_rv $$ [$Hacc $HD] as %rv %rvErr %Hrv
  (try wp_auto)
  wp_apply wp_parse as %rvInt %parseErr _
  (try wp_auto)
  wp_apply (lc := 2) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  iunfold tsP at HP
  icases HP with ⟨%σ, %ph, Hst, Hgp, Hph, #Hpers, %Hok⟩
  (try wp_auto)
  ihave #Hobj : okNil OK obj $$ []
  · iunfold okNil; iright; iexact HOK
  wp_apply wp_upd $$ [$Hidx $Him $Hph $Hpers $Hobj] as ⟨%ix', Hph, %Hok'⟩
  · ipureintro; exact Hok
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrvf, Hind, Hix, Hfv⟩
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      structFieldRef threadSafeMap go!"rv" c ↦ ((rvOf obj).getD σ.rv) ∗
      rv_ptr ↦ rv ∗ parseErr_ptr ↦ parseErr ∗ rvInt_ptr ↦ rvInt ∗
      c_ptr ↦ c)))
    $$ [Hrvf rv parseErr rvInt c]
  · cases hr : rvOf obj with
    | none =>
      rw [hr] at Hrv
      obtain ⟨_, hne⟩ := Hrv
      cases rvErr with
      | nil => exact absurd rfl hne
      | ok e =>
        (try wp_auto)
        iframe
        ipureintro; rfl
    | some r =>
      rw [hr] at Hrv
      obtain ⟨rfl, rfl⟩ := Hrv
      (try wp_auto)
      cases parseErr with
      | ok e =>
        (try wp_auto)
        iframe
        ipureintro; rfl
      | nil =>
        (try wp_auto)
        cases g with
        | nil => iunfold gaugeOk at Hgok; icases Hgok with ⟨⟩
        | ok gi =>
          iunfold gaugeOk at Hgok
          (try wp_auto)
          wp_apply Hgok
          (try wp_auto)
          iframe
          ipureintro; rfl
  iintro %v ⟨%hv, Hrvf, rv, parseErr, rvInt, c⟩
  subst hv
  imod storeSt_update γ σ (fun σ => σ.update key obj (rvOf obj)) _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
  imod ghostVar_update ({ ph with ix := ix' } : Ph) $$ Hgp with Hgp
  (try wp_auto)
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, #Hits⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hst Hgp Hitems Hil Hind Hix Hfv Hrvf]
  · inext
    iunfold tsP
    iexists (σ.update key obj (rvOf obj)), ({ ph with ix := ix' } : Ph)
    iframe
    isplitl
    · iunfold tsPhys; iframe
    isplitr
    · iunfold tsPers
      have hf : St.fns Fam (σ.update key obj (rvOf obj)) = St.fns Fam σ := rfl
      have hi : (σ.update key obj (rvOf obj)).items = <[key := obj]> σ.items := rfl
      rw [hf, hi]
      isplitr
      · iexact Hfns
      · iapply (BigSepM.bigSepM_insert_elim (Φ := fun _ o => okNil (GF := GF) OK o)
          (m := σ.items) (i := key) (x := obj)) $$ Hobj Hits
    · ipureintro; exact Hok'
  (try wp_auto)
  iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
