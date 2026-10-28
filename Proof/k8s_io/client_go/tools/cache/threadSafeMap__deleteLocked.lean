/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__deleteLocked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__deleteLocked
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

theorem threadSafeMap.deleteLocked.wp_proof
    (wp_upd : storeIndex.updateIndices.spec (GF := GF) (hG := hG)) :
    threadSafeMap.deleteLocked.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam σ ph iv key
  wp_start as ⟨#Hidx, #Him, Hph, #Hpers, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrv, Hind, Hix, Hfv⟩
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, #Hits, #Hiv⟩
  (try wp_auto)
  wp_apply (wp_map_lookup2 go.string (go.GoType.InterfaceType []) ph.il σ.items key)
    $$ [$Hil] as Hil
  cases hk : σ.items !! key with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    (try wp_auto)
    have hd : GMap.delete key σ.items = σ.items := by
      ext k; simp only [GMap.lookup_delete_iff]; split <;> simp_all
    iapply HΦ
    iexists ph.ix, iv
    iunfold tsPhys
    rw [hd]
    iframe
    isplitr
    · iunfold tsPers; iframe #
    · ipureintro; exact Hok
  | some o =>
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    (try wp_auto)
    ihave #Hold : okNil OK o $$ []
    · iapply BigSepM.bigSepM_lookup hk $$ Hits
    ihave #Hnil : okNil OK GoInterface.nil $$ []
    · iunfold okNil; ileft; ipureintro; rfl
    ihave #Hov := itemsIv_lookup _ σ.items iv key Hok.2 $$ Hiv
    have ho : objAt σ.items key = o := by unfold objAt; rw [hk]; rfl
    rw [ho]
    wp_apply (wp_upd γ.idx γ.im ph.ip DFrac.discard 1 ph.fv (σ.fns Fam) ph.ix OK iv key
        o GoInterface.nil)
      $$ [$Him $Hfv $Hfns $Hold $Hnil $Hov $Hind $Hix] as ⟨%ix', %vs, -, Hfv, Hind, Hix, #Hvs, %Hok'⟩
    · ipureintro; exact Hok.1
    (try wp_auto)
    wp_apply (wp_mapDelete ph.il σ.items key go.string (go.GoType.InterfaceType [])) $$ [$Hil] as Hil
    (try wp_auto)
    iapply HΦ
    iexists ix', <[key := vs]> iv
    ihave %hnil := valsOk_nil_pure _ GoInterface.nil vs $$ Hvs
    iunfold tsPhys
    iframe
    have hfns : St.fns Fam { items := GMap.delete key σ.items, rv := σ.rv, fnIds := σ.fnIds } =
        St.fns Fam σ := rfl
    isplitr
    · iunfold tsPers
      simp only []
      rw [hfns]
      iframe #
      isplitr
      · iapply (BigSepM.bigSepM_forall (Φ := fun (_ : GoString) o => okNil OK o)).2
        iintro %k %o' %hk'
        change (GMap.delete key σ.items) !! k = some o' at hk'
        by_cases hkk : k = key
        · subst hkk; rw [GMap.lookup_delete] at hk'; cases hk'
        · rw [GMap.lookup_delete_ne _ (Ne.symm hkk)] at hk'
          iapply (BigSepM.bigSepM_lookup hk') $$ Hits
      · iapply itemsIv_delete $$ Hiv
    · ipureintro
      exact ⟨Hok'.1, ivWf_delete Hok.2 (fun n =>
        vs_wf Hok.2 hnil Hok'.2 n (Or.inl rfl))⟩

end proof

end cache
end EtcdGrove
end Perennial
