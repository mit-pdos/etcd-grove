/-
Proof of `Spec/k8s_io/client_go/tools/cache/threadSafeMap__updateLocked.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.threadSafeMap__updateLocked
public import Spec.k8s_io.client_go.tools.cache.storeIndex__updateIndices

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

theorem threadSafeMap.updateLocked.wp_proof
    (wp_upd : storeIndex.updateIndices.spec (GF := GF) (hG := hG)) :
    threadSafeMap.updateLocked.spec (GF := GF) (hG := hG) := by
  intro c γ OK Fam σ ph iv key obj
  wp_start as ⟨#Hidx, #Him, Hph, #Hpers, #Hobj, %Hok⟩
  iunfold tsPhys at Hph
  icases Hph with ⟨Hitems, Hil, Hrv, Hind, Hix, Hfv⟩
  iunfold tsPers at Hpers
  icases Hpers with ⟨#Hfns, #Hits, #Hiv⟩
  (try wp_auto)
  wp_apply (wp_map_lookup1 go.string (go.GoType.InterfaceType []) ph.il σ.items key)
    $$ [$Hil] as Hil
  (try wp_auto)
  wp_apply (wp_mapInsert go.string ph.il σ.items key obj) $$ [$Hil] as Hil
  (try wp_auto)
  ihave #Hold : okNil OK ((σ.items !! key).getD GoInterface.nil) $$ []
  · skip
    cases hk : σ.items !! key with
    | none => iunfold okNil; ileft; ipureintro; rfl
    | some o => iapply BigSepM.bigSepM_lookup hk $$ Hits
  have hlk := itemsIv_lookup (GF := GF) (σ.fns Fam) σ.items iv key Hok.2
  unfold objAt at hlk
  ihave #Hov := hlk $$ Hiv
  wp_apply (wp_upd γ.idx γ.im ph.ip DFrac.discard 1 ph.fv (σ.fns Fam) ph.ix OK iv key
      ((σ.items !! key).getD GoInterface.nil) obj)
    $$ [$Him $Hfv $Hfns $Hold $Hobj $Hov $Hind $Hix] as ⟨%ix', %vs, -, Hfv, Hind, Hix, #Hvs, %Hok'⟩
  · ipureintro; exact Hok.1
  (try wp_auto)
  iapply HΦ
  iexists ix', <[key := vs]> iv
  ihave %hnil := valsOk_nil_pure _ obj vs $$ Hvs
  iunfold tsPhys
  iframe
  have hfns : St.fns Fam { items := <[key := obj]> σ.items, rv := σ.rv, fnIds := σ.fnIds } =
      St.fns Fam σ := rfl
  isplitr
  · iunfold tsPers
    simp only []
    rw [hfns]
    iframe #
    isplitr
    · iapply (BigSepM.bigSepM_forall (Φ := fun (_ : GoString) o => okNil OK o)).2
      iintro %k %o %hk
      change (<[key := obj]> σ.items) !! k = some o at hk
      by_cases hkk : k = key
      · subst hkk
        simp only [GMap.lookup_insert, Option.some.injEq] at hk
        subst hk
        iexact Hobj
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)] at hk
        iapply (BigSepM.bigSepM_lookup hk) $$ Hits
    · iapply itemsIv_insert $$ [$Hiv $Hvs]
  · ipureintro; exact ⟨Hok'.1, ivWf_insert Hok.2 (vs_wf Hok.2 hnil Hok'.2)⟩

end proof

end cache
end EtcdGrove
end Perennial
