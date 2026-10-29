/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__DeleteWithObject.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__DeleteWithObject
public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__deleteLocked
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The write lock's resources back, at the state after a delete. -/
theorem tsP_after_delete (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (σ : St) (ph : Ph) (key : GoString) (rvo : Option GoString) (ix' : Ix) (iv' : IV) :
    ghostVar γ.st (1 : Qp).half (σ.delete key rvo) ∗ ghostVar γ.ph 1 { ph with ix := ix' } ∗
      structFieldRef threadSafeMap go!"items" c ↦ ph.il ∗
      ph.il ↦$ GMap.delete key σ.items ∗
      structFieldRef threadSafeMap go!"rv" c ↦ rvo.getD σ.rv ∗
      structFieldRef storeIndex go!"indices" γ.idx ↦ ph.ip ∗
      ownIx ph.ip (DFrac.own 1) ix' ∗ γ.im ↦$ ph.fv ∗
      tsPers OK Fam { σ with items := GMap.delete key σ.items } { ph with ix := ix' } iv' ∗
      ⌜ixOk (σ.fns Fam) iv' ix' ∧ ivWf (σ.fns Fam) (GMap.delete key σ.items) iv'⌝ ⊢
    tsP c γ OK Fam 1 := by
  iintro ⟨Hst, Hgp, Hitems, Hil, Hrv, Hind, Hix, Hfv, #Hpers, %Hok⟩
  iunfold tsP
  iexists σ.delete key rvo, { ph with ix := ix' }, iv'
  iframe
  isplitl
  · iunfold tsPhys; iframe
  have hp : tsPers OK Fam (σ.delete key rvo) { ph with ix := ix' } iv' =
      tsPers OK Fam { σ with items := GMap.delete key σ.items } { ph with ix := ix' } iv' := rfl
  rw [hp]
  isplitr
  · iexact Hpers
  · ipureintro; exact Hok

theorem threadSafeMap.DeleteWithObject.wp_proof
    (wp_rv : rvFromObject.spec (GF := GF) (hG := hG))
    (wp_parse : parseRVForMetricsWithTruncation.spec (GF := GF) (hG := hG))
    (wp_del : threadSafeMap.deleteLocked.spec (GF := GF) (hG := hG)) :
    threadSafeMap.DeleteWithObject.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam D rvOf key obj
  iintro %Φ ⟨#Hpkg, #Hc, #Hobj, #Hacc⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hc
  icases Hc with ⟨%mp, %g, #Hidx, #Him, #Hmp, #Hg, #Hgok, #Hguard⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- the object's resource version, if not `nil`
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ obj_ptr ↦ obj ∗
      ∃ (rv : GoString) (rvErr : GoInterface) (rvInt : w64) (parseErr : GoInterface),
        rv_ptr ↦ rv ∗ rvErr_ptr ↦ rvErr ∗ rvInt_ptr ↦ rvInt ∗ parseErr_ptr ↦ parseErr ∗
        ⌜obj ≠ interface.nil → match rvOf obj with
          | some r => rv = r ∧ rvErr = interface.nil
          | none => rv = [] ∧ rvErr ≠ interface.nil⌝)))
    $$ [obj rv rvErr rvInt parseErr]
  · cases obj with
    | nil =>
      (try wp_auto)
      iframe
      isplitr
      · ipureintro; rfl
      iframe
      ipureintro; intro h; exact absurd rfl h
    | ok oi =>
      ihave #Hacc' := Hacc $$ %(by simp)
      iunfold okNil at Hobj
      icases Hobj with (%h | #HOK)
      · cases h
      (try wp_auto)
      wp_apply wp_rv $$ [$Hacc' $HOK] as %rv %rvErr %Hrv
      (try wp_auto)
      wp_apply wp_parse as %rvInt %parseErr _
      (try wp_auto)
      iframe
      isplitr
      · ipureintro; rfl
      iframe
      ipureintro; intro _; exact Hrv
  iintro %v ⟨%hv, obj, %rv, %rvErr, %rvInt, %parseErr, rv, rvErr, rvInt, parseErr, %Hrv⟩
  subst hv
  (try wp_auto)
  wp_apply (lc := 2) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  iunfold tsP at HP
  icases HP with ⟨%σ, %ph, %iv, Hst, Hgp, Hph, #Hpers, %Hok⟩
  (try wp_auto)
  wp_apply wp_del $$ [$Hidx $Him $Hph $Hpers] as ⟨%ix', %iv', Hph, #Hpers', %Hok'⟩
  · ipureintro; exact Hok
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrvf, Hind, Hix, Hfv⟩
  (try wp_auto)
  -- the resource version, if the object has one
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      structFieldRef threadSafeMap go!"rv" c ↦ ((rvOfObj rvOf obj).getD σ.rv))))
    $$ [- HAU Hst Hgp Hwl Hitems Hil Hind Hix Hfv defer]
  · cases obj with
    | nil =>
      have hro : rvOfObj rvOf GoInterface.nil = none := by simp [rvOfObj]
      rw [hro]
      (try wp_auto)
      iframe
      ipureintro; rfl
    | ok oi =>
      have hro : rvOfObj rvOf (GoInterface.ok oi) = rvOf (GoInterface.ok oi) := by simp [rvOfObj]
      rw [hro]
      have Hrv' := Hrv (by simp)
      cases hr : rvOf (GoInterface.ok oi) with
      | none =>
        rw [hr] at Hrv'
        obtain ⟨_, hne⟩ := Hrv'
        cases rvErr with
        | nil => exact absurd rfl hne
        | ok e =>
          (try wp_auto)
          iframe
          ipureintro; rfl
      | some r =>
        rw [hr] at Hrv'
        obtain ⟨rfl, rfl⟩ := Hrv'
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
  iintro %v ⟨%hv, Hrvf⟩
  subst hv
  imod storeSt_update γ σ (fun σ => σ.delete key (rvOfObj rvOf obj)) _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
  imod ghostVar_update ({ ph with ix := ix' } : Ph) $$ Hgp with Hgp
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hst Hgp Hitems Hil Hind Hix Hfv Hrvf]
  · inext
    iapply tsP_after_delete c γ OK Fam σ ph key (rvOfObj rvOf obj) ix' iv'
    iframe; iframe #
    ipureintro; exact Hok'
  (try wp_auto)
  iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
