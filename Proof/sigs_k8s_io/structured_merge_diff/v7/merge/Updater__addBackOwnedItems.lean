/-
`merge.Updater.addBackOwnedItems`:
proved (Prove, 2026-11-21): the `for range` over the managers builds `managedAtVersion`, empty
(no manager) or one entry at the pruned version holding the union of the sets visited (`mfVis`);
then one `addBackOwnedItemsForVersion` at that version, and the second loop ranges over an empty map.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `fieldpath.versionedSet.Set`, `fieldpath.versionedSet.APIVersion`,
`fieldpath.Set.Union`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackOwnedItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackOwnedItemsForVersion
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsM1

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

theorem merge.Updater.addBackOwnedItems.wp_proof
    (h_NewSet : fieldpath.NewSet.spec (GF := GF))
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF))
    (h_Updater_addBackOwnedItemsForVersion : merge.Updater.addBackOwnedItemsForVersion.spec (GF := GF)) :
    merge.Updater.addBackOwnedItems.spec (GF := GF) :=
    fun u cv igf igfl rion sc S t mp merged pp pruned pv mfm mf mgr => by
  wp_start as ⟨#Hu, #Hcv, #Hm, #Hp, Hmf, %hver, %hpre⟩
  obtain ⟨hms, hps, hman, hconf⟩ := hpre
  ihave ⟨%M, HM, %hM, #HE, Hclose⟩ := ownMF_access_law_holds mfm mf $$ Hmf
  obtain ⟨hMs, hMk⟩ := hM
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %mav Hmav
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (j : Int) => iprop(∃ (A : GMap GoString Loc)
      (y : GoInterface),
      "%Hj" ∷ ⌜0 ≤ j⌝ ∗
      "HA" ∷ (⌜(∀ v, A !! v = none) ∧ j = 0⌝ ∨ ∃ (p : Loc) (U : PathSet),
        ⌜0 < j ∧ A !! pv = some p ∧ (∀ v, v ≠ pv → A !! v = none) ∧
          ∀ q, q ∈ U ↔ mfVis mf (keys.take j.toNat) q⌝ ∗ isSet p U) ∗
      "Hmav" ∷ mav ↦$ A ∗
      "managedAtVersion" ∷ managedAtVersion_ptr ↦ mav ∗
      "managerSet" ∷ managerSet_ptr ↦ y)) $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hmav managedAtVersion managerSet]
  · iexists (∅ : GMap GoString Loc), _
    simp only [named]
    iframe
    isplitr
    · ipureintro; omega
    ileft; ipureintro; exact ⟨fun v => GMap.lookup_empty v, trivial⟩
  isplitr
  · imodintro
    iintro %j %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    obtain ⟨e, he⟩ : ∃ e, mf.get key = some e :=
      Option.isSome_iff_exists.1 (by rw [← hMk, Hv]; rfl)
    have hev : e.version = pv := hver key e he
    ihave #Hve := HE $$ %key %v %e %(⟨Hv, he⟩)
    ihave ⟨%vv, %hvv⟩ := isVSet_concrete_law_holds v e $$ Hve
    subst hvv
    wp_auto
    wp_apply (h_versionedSet_APIVersion vv e) as %ver %hver'
    · iexact Hve
    subst hver'
    rw [hev]
    wp_apply (wp_map_lookup2 _ _ mav A pv) $$ Hmav as Hmav
    icases HA with (⟨%hA0, %hj0⟩ | ⟨%p, %U, %hA, #HU⟩)
    · rw [hA0 pv]
      wp_auto
      ihave Hnil := ownSlice_nil (V := GoSlice) (GF := GF) DFrac.discard
      wp_apply (h_NewSet slice.nil DFrac.discard DFrac.discard [] []) $$ [$Hnil] as %p0 ⟨-, -, Hp0⟩
      · unfold isPathsF; itrivial
      wp_apply (h_versionedSet_APIVersion vv e) as %ver %hver'
      · iexact Hve
      subst hver'
      rw [hev]
      wp_apply (wp_mapInsert _ mav A pv p0) $$ Hmav as Hmav
      imod (ownSet_persist_law_holds _ _) $$ Hp0 with #Hp0
      wp_apply (h_versionedSet_Set vv e) as %sp #Hsp
      · iexact Hve
      wp_apply (h_versionedSet_APIVersion vv e) as %ver %hver'
      · iexact Hve
      subst hver'
      rw [hev]
      wp_apply (wp_map_lookup1 _ _ mav _ pv) $$ Hmav as Hmav
      wp_apply (h_Set_Union p0 sp _ _) as %un #Hun
      · isplitr
        · iexact Hp0
        · iexact Hsp
      wp_apply (h_versionedSet_APIVersion vv e) as %ver %hver'
      · iexact Hve
      subst hver'
      rw [hev]
      wp_apply (wp_mapInsert _ mav _ pv un) $$ Hmav as Hmav
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      simp only [named]
      iframe
      isplitr
      · ipureintro; omega
      iright
      iexists un, _
      isplitr
      · ipureintro
        refine ⟨by omega, GMap.lookup_insert _ _ _, fun v hv => ?_, ?_⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hv), GMap.lookup_insert_ne _ _ (Ne.symm hv)]
          exact hA0 v
        · apply mfVis_step mf keys j key e (PathSet.ofList []) Hj Hkey he
          intro q
          subst hj0
          simp only [Int.toNat_zero, List.take_zero]
          rw [PathSet_mem_ofList_law_holds]
          simp [mfVis_nil]
      iexact Hun
    · obtain ⟨-, hAp, hAo, hU⟩ := hA
      rw [hAp]
      simp only [Option.isSome_some, decide_true, Bool.not_true]
      wp_auto
      wp_apply (h_versionedSet_Set vv e) as %sp #Hsp
      · iexact Hve
      wp_apply (h_versionedSet_APIVersion vv e) as %ver %hver'
      · iexact Hve
      subst hver'
      rw [hev]
      wp_apply (wp_map_lookup1 _ _ mav _ pv) $$ Hmav as Hmav
      rw [hAp, Option.getD_some]
      wp_apply (h_Set_Union p sp _ _) as %un #Hun
      · isplitr
        · iexact HU
        · iexact Hsp
      wp_apply (h_versionedSet_APIVersion vv e) as %ver %hver'
      · iexact Hve
      subst hver'
      rw [hev]
      wp_apply (wp_mapInsert _ mav _ pv un) $$ Hmav as Hmav
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      simp only [named]
      iframe
      isplitr
      · ipureintro; omega
      iright
      iexists un, _
      isplitr
      · ipureintro
        refine ⟨by omega, GMap.lookup_insert _ _ _, fun v hv => ?_, ?_⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hv)]
          exact hAo v hv
        · exact mfVis_step mf keys j key e U Hj Hkey he hU
      iexact Hun
  iintro HP HM
  iNamed HP
  ihave HMF := Hclose $$ %M %mf HM %(⟨hMs, hMk⟩) HE
  wp_auto
  wp_apply (wp_map_lookup2 _ _ mav A pv) $$ Hmav as Hmav
  icases HA with (⟨%hA0, %hsz⟩ | ⟨%p, %U, %hA, #HU⟩)
  · -- no manager
    have hkeys : keys = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hmf : mf = [] := by
      cases mf with
      | nil => rfl
      | cons me rest =>
        exfalso
        have h1 := hMk me.1
        have h2 := (Hkset me.1)
        rw [hkeys] at h2
        simp [MF.get, lookupKV] at h1
        simp [h1] at h2
    subst hmf
    rw [hA0 pv]
    wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(True)) $$ Hmav
    iintro %keys2 ⟨%Hk2, -, -⟩
    isplitr
    · itrivial
    isplitr
    · imodintro
      iintro %j2 %key2 %v2 ⟨%Hkey2, %Hv2⟩ -
      exfalso
      rw [hA0 key2] at Hv2; cases Hv2
    iintro - Hmav
    wp_auto
    iapply HΦ
    iframe HMF
    isplitr
    · ipureintro; rfl
    rw [show addBackOwnedMF S t merged pruned [] = pruned from rfl]
    iexact Hp
  · obtain ⟨hpos, hAp, hAo, hU⟩ := hA
    rw [Int.toNat_natCast, ← Hklen, List.take_length] at hU
    have hmf : mf ≠ [] := by
      intro hmf
      subst hmf
      obtain ⟨k, hk⟩ : ∃ k, k ∈ keys := List.exists_mem_of_length_pos (by omega)
      have := (Hkset k).1 hk
      rw [hMk k] at this
      simp [MF.get, lookupKV] at this
    have hUeq : U = mfUnion mf := FSet.ext' (fun q => by
      rw [hU, mfVis_all mf keys hMs (fun k => by rw [Hkset k, hMk k])])
    subst hUeq
    have habo : addBackOwnedMF S t merged pruned mf = addBackOwned S t merged pruned (mfUnion mf) := by
      cases mf with
      | nil => exact absurd rfl hmf
      | cons _ _ => rfl
    rw [habo] at hconf ⊢
    rw [hAp]
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    wp_auto
    wp_apply (h_Updater_addBackOwnedItemsForVersion u cv igf igfl rion sc S t mp merged pp pruned pv p
      (mfUnion mf)) as %mp' %pp' %err' ⟨⟨%hmp', %herr'⟩, Hpp'⟩
    · iframe Hu Hcv Hm Hp HU
      ipureintro; exact ⟨hms, hps, hman, hconf⟩
    subst hmp' herr'
    wp_auto
    wp_apply (wp_mapDelete mav A pv) $$ Hmav as Hmav
    have hdel : ∀ v, (GMap.delete pv A) !! v = none := by
      intro v
      by_cases hv : v = pv
      · subst hv; exact GMap.lookup_delete _ _
      · rw [GMap.lookup_delete_ne _ (Ne.symm hv)]; exact hAo v hv
    try wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(True)) $$ Hmav
    iintro %keys2 ⟨%Hk2, -, -⟩
    isplitr
    · itrivial
    isplitr
    · imodintro
      iintro %j2 %key2 %v2 ⟨%Hkey2, %Hv2⟩ -
      exfalso
      rw [hdel key2] at Hv2; cases Hv2
    iintro - Hmav
    wp_auto
    iapply HΦ
    iframe HMF
    isplitr
    · ipureintro; rfl
    iexact Hpp'

end proof

end smd
end EtcdGrove
end Perennial
