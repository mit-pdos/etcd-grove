/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__Replace.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__Replace
public import Spec.k8s_io.client_go.tools.cache.parseRVForMetricsWithTruncation
public import Spec.k8s_io.client_go.tools.cache.storeIndex__reset
public import Spec.k8s_io.client_go.tools.cache.storeIndex__updateIndices

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

theorem threadSafeMap.Replace.wp_proof
    (wp_parse : parseRVForMetricsWithTruncation.spec (GF := GF) (hG := hG))
    (wp_reset : storeIndex.reset.spec (GF := GF) (hG := hG))
    (wp_upd : storeIndex.updateIndices.spec (GF := GF) (hG := hG)) :
    threadSafeMap.Replace.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam nl its rv
  iintro %Φ ⟨#Hpkg, #Hc, Hnl, #Hits'⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTS at Hc
  icases Hc with ⟨%mp, %g, #Hidx, #Him, #Hmp, #Hg, #Hgok, #Hguard⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ resourceVersion_ptr ↦ rv ∗
      ∃ (rvInt : w64) (parseErr : GoInterface), rvInt_ptr ↦ rvInt ∗ parseErr_ptr ↦ parseErr)))
    $$ [resourceVersion rvInt parseErr]
  · wp_if_destruct
    · (try wp_auto)
      iframe
    · (try wp_auto)
      wp_apply wp_parse as %n %err _
      (try wp_auto)
      iframe
      try (ipureintro; rfl)
  iintro %v ⟨%hv, resourceVersion, %rvInt, %parseErr, rvInt, parseErr⟩
  subst hv
  (try wp_auto)
  wp_apply (lc := 2) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  iunfold tsP at HP
  icases HP with ⟨%σ, %ph, %iv, Hst, Hgp, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrvf, Hind, Hix, Hfv⟩
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, -, -⟩
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ c_ptr ↦ c)))
    $$ [- HAU Hst Hgp Hwl Hitems Hil Hind Hix Hfv Hrvf Hnl defer]
  · cases parseErr with
    | ok e =>
      (try wp_auto)
      iframe
      try (ipureintro; rfl)
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
        try (ipureintro; rfl)
  iintro %v ⟨%hv, c⟩
  subst hv
  (try wp_auto)
  wp_apply wp_reset $$ [$Hind] as ⟨%ip', Hind, Hix'⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (p : Int) => iprop(∃ (x : GoInterface)
      (y : GoString) (ixp : Ix) (ivp : IV),
      "%Hp" ∷ ⌜0 ≤ p⌝ ∗
      "%Hokp" ∷ ⌜ixOk (σ.fns Fam) ivp ixp ∧
        ivWf (σ.fns Fam) (restrictK its (keys.take p.toNat)) ivp⌝ ∗
      "#Hivp" ∷ itemsIv (σ.fns Fam) (restrictK its (keys.take p.toNat)) ivp ∗
      "item" ∷ item_ptr ↦ x ∗ "key" ∷ key_ptr ↦ y ∗ "c" ∷ c_ptr ↦ c ∗
      "Hind" ∷ structFieldRef storeIndex go!"indices" γ.idx ↦ ip' ∗
      "Hix" ∷ ownIx ip' (DFrac.own 1) ixp ∗
      "Hfv" ∷ γ.im ↦$ ph.fv)) $$ Hnl
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [item key c Hind Hix' Hfv]
  · iexists _, _, ∅, ∅
    simp only [named, Int.toNat_zero, List.take_zero, restrictK_nil]
    iframe
    isplitr
    · ipureintro; exact Int.le_refl _
    isplitr
    · ipureintro; exact ⟨ixOk_empty _, ivWf_empty _ _⟩
    · iunfold itemsIv; iapply BigSepM.bigSepM_empty.2; itrivial
  isplitr
  · imodintro
    iintro %p %k %o ⟨%Hkey, %Ho⟩ HP
    iNamed HP
    ihave #Hoko : okNil OK o $$ []
    · iapply BigSepM.bigSepM_lookup Ho $$ Hits'
    ihave #Hnil : okNil OK GoInterface.nil $$ []
    · iunfold okNil; ileft; ipureintro; rfl
    have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
      rw [show (p + 1).toNat = p.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    have hnd : k ∉ keys.take p.toNat := by
      intro hm
      have hd : k ∈ keys.drop p.toNat := by
        rw [List.mem_iff_getElem?]
        exact ⟨0, by rw [List.getElem?_drop]; simpa using Hkey⟩
      have hnod := List.nodup_append.1 ((List.take_append_drop p.toNat keys).symm ▸ Hknodup)
      exact hnod.2.2 k hm k hd rfl
    have hold0 : objAt (restrictK its (keys.take p.toNat)) k = GoInterface.nil := by
      rw [objAt_restrictK]; simp [hnd]
    have hlk := itemsIv_lookup (GF := GF) (σ.fns Fam) _ ivp k Hokp.2
    rw [hold0] at hlk
    ihave #Hov := hlk $$ Hivp
    wp_auto
    wp_apply (wp_upd γ.idx γ.im ip' DFrac.discard 1 ph.fv (σ.fns Fam) ixp OK ivp k
        GoInterface.nil o) $$ [$Him $Hfv $Hfns $Hnil $Hoko $Hov $Hind $Hix]
      as ⟨%ix', %vs, -, Hfv, Hind, Hix, #Hvs, %Hok'⟩
    · ipureintro; exact Hokp.1
    ihave %hnil := valsOk_nil_pure _ o vs $$ Hvs
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists o, k, ix', <[k := vs]> ivp
    simp only [named]
    rw [Htake, restrictK_snoc its _ k o Ho]
    iframe
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; exact ⟨Hok'.1, ivWf_insert Hokp.2 (vs_wf Hokp.2 hnil Hok'.2)⟩
    · iapply itemsIv_insert $$ [$Hivp $Hvs]
  iintro HP Hnl
  iNamed HP
  have hall : restrictK its (keys.take (GMap.size its : Int).toNat) = its := by
    rw [Int.toNat_natCast, ← Hklen, List.take_length]
    exact restrictK_all its keys (fun k hk => (Hkset k).2 hk)
  rw [hall] at Hokp
  imod storeSt_update γ σ (fun σ => σ.replace its rv) _ $$ [$Hst $HAU] with ⟨Hst, HK⟩
  imod ghostVar_update (⟨nl, ip', ixp, ph.fv⟩ : Ph) $$ Hgp with Hgp
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hst Hgp Hitems Hnl Hind Hix Hfv Hrvf]
  · inext
    iunfold tsP
    iexists σ.replace its rv, ⟨nl, ip', ixp, ph.fv⟩, ivp
    iframe
    isplitl
    · iunfold tsPhys; iframe
    isplitr
    · iunfold tsPers
      have hf : St.fns Fam (σ.replace its rv) = St.fns Fam σ := rfl
      have hi : (σ.replace its rv).items = its := rfl
      rw [hf, hi]
      isplitr
      · iexact Hfns
      isplitr
      · iexact Hits'
      · have hH : itemsIv (GF := GF) (σ.fns Fam)
            (restrictK its (keys.take (GMap.size its : Int).toNat)) ivp ⊢
            itemsIv (σ.fns Fam) its ivp := by rw [hall]
        iapply hH $$ Hivp
    · ipureintro; exact Hokp
  (try wp_auto)
  iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
