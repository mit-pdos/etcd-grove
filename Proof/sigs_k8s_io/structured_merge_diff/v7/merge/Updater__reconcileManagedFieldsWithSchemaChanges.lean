/-
`merge.Updater.reconcileManagedFieldsWithSchemaChanges`:
proved (Prove, 2026-11-21): a `for range` over the read-only input map (`wp_map_for_range`) filling
a fresh owned map; each manager's set below `2 ^ 63` paths from the union's node bound
(`mf_entry_cardLt`).
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `typed.ReconcileFieldSetWithSchema`, `fieldpath.versionedSet.Set`,
`fieldpath.versionedSet.APIVersion`, `fieldpath.versionedSet.Applied`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__reconcileManagedFieldsWithSchemaChanges
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Applied
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ReconcileFieldSetWithSchema
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

theorem merge.Updater.reconcileManagedFieldsWithSchemaChanges.wp_proof
    (h_NewVersionedSet : fieldpath.NewVersionedSet.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Applied : fieldpath.versionedSet.Applied.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF))
    (h_ReconcileFieldSetWithSchema : typed.ReconcileFieldSetWithSchema.spec (GF := GF)) :
    merge.Updater.reconcileManagedFieldsWithSchemaChanges.spec (GF := GF) :=
    fun u cv igf igfl rion sc S t lp live mfm mf => by
  wp_start as ⟨#Hu, #Hcv, #Hl, #Hmf, %hsmall⟩
  unfold isUpdater isIdentityConverter
  icases Hcv with ⟨%T, %cvv, %hcv, #HConv, #HMiss⟩
  subst hcv
  iStructNamed Hu
  ihave ⟨%M, #HM, %hM, #HE⟩ := isMF_read mfm mf $$ Hmf
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %r Hr
  ihave Hr := ownMF_empty_law_holds r $$ Hr
  ihave ⟨%M0, Hr, %h0, -, Hclose⟩ := ownMF_access_law_holds r MF.none $$ Hr
  obtain ⟨hMs, hMk⟩ := hM
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (j : Int) => iprop(∃ (R : GMap GoString GoInterface)
      (x : GoString) (y : GoInterface),
      "%Hj" ∷ ⌜0 ≤ j⌝ ∗
      "%HR" ∷ ⌜∀ k, (R !! k).isSome = true ↔ k ∈ keys.take j.toNat⌝ ∗
      "#HRE" ∷ □ (∀ k i e, ⌜R !! k = some i ∧ mf.get k = some e⌝ -∗
        isVSet i { e with set := reconcile S t e.set }) ∗
      "Hr" ∷ r ↦$ R ∗
      "Hclose" ∷ (∀ (M' : GMap GoString GoInterface) (mf' : MF), r ↦$ M' -∗
        ⌜keysSorted mf' = true ∧ ∀ k, (M' !! k).isSome = (mf'.get k).isSome⌝ -∗
        □ (∀ k i e, ⌜M' !! k = some i ∧ mf'.get k = some e⌝ -∗ isVSet i e) -∗ ownMF r mf') ∗
      "s" ∷ s_ptr ↦ u ∗
      "liveObject" ∷ liveObject_ptr ↦ lp ∗
      "result" ∷ result_ptr ↦ r ∗
      "versionedSet" ∷ versionedSet_ptr ↦ y ∗
      "manager" ∷ manager_ptr ↦ x ∗
      "res0" ∷ «$res0_ptr» ↦ zero_val GoMap ∗
      "res1" ∷ «$res1_ptr» ↦ GoInterface.nil)) $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hr Hclose s liveObject result versionedSet manager «$res0» «$res1»]
  · iexists M0, _, _
    simp only [named]
    iframe
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro
      intro k
      have := h0.2 k
      simp [MF.none, MF.get, lookupKV] at this
      simp [this]
    imodintro
    iintro %k %i %e ⟨%hk, -⟩
    exfalso
    have := h0.2 k
    simp [MF.none, MF.get, lookupKV, hk] at this
  isplitr
  · imodintro
    iintro %j %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    obtain ⟨e, he⟩ : ∃ e, mf.get key = some e :=
      Option.isSome_iff_exists.1 (by rw [← hMk, Hv]; rfl)
    ihave #Hve := HE $$ %key %v %e %(⟨Hv, he⟩)
    ihave ⟨%vv, %hvv⟩ := isVSet_concrete_law_holds v e $$ Hve
    subst hvv
    wp_auto
    wp_apply (h_versionedSet_APIVersion vv e) as %ver %hver
    · iexact Hve
    subst hver
    try wp_auto
    wp_bind (App (App (Val #(methods T go!"Convert" cvv)) (Val #lp)) (Val #e.version))
    iapply HConv
    inext
    wp_auto
    wp_bind (App (Val #(methods T go!"IsMissingVersionError" cvv)) (Val #(interface.nil : GoInterface)))
    iapply HMiss
    inext
    wp_auto
    wp_apply (h_versionedSet_Set vv e) as %sp #Hsp
    · iexact Hve
    try wp_auto
    ihave %hne := isSet_ne_law_holds _ _ $$ Hsp
    wp_apply (h_ReconcileFieldSetWithSchema sp lp sc S t live e.set) as %rc %rerr ⟨%hrerr, Hrc⟩
    · iframe Hsp Hl; ipureintro; exact mf_entry_cardLt mf key e he hne hsmall
    subst hrerr
    wp_auto
    by_cases hrc : rc = null
    · icases Hrc with (⟨%hn, %hid⟩ | Hrc)
      · subst hn
        simp only [decide_true, Bool.not_true]
        wp_auto
        wp_apply (wp_mapInsert go.string r R key (interface.mkOk fieldpath.versionedSet.ty #vv)) $$ Hr as Hr
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _, key, _
        simp only [named]
        iframe
        isplitr
        · ipureintro; omega
        isplitr
        · ipureintro; exact take_dom_step R keys j key _ Hj Hkey HR
        imodintro
        iintro %k %i %e' ⟨%hk, %he'⟩
        by_cases hkk : key = k
        · subst hkk
          rw [GMap.lookup_insert] at hk; cases hk
          rw [he] at he'; cases he'
          rw [hid]
          iexact Hve
        · rw [GMap.lookup_insert_ne _ _ hkk] at hk
          iapply HRE $$ %k %i %e'; ipureintro; exact ⟨hk, he'⟩
      · subst hrc
        ihave %hne' := isSet_not_null _ _ $$ Hrc
        exact absurd rfl hne'
    · icases Hrc with (⟨%hn, -⟩ | #Hrc)
      · exact absurd hn hrc
      simp only [hrc, decide_false, Bool.not_false]
      wp_auto
      wp_apply (h_versionedSet_APIVersion vv e) as %ver %hver
      · iexact Hve
      subst hver
      wp_apply (h_versionedSet_Applied vv e) as %ap %hap
      · iexact Hve
      subst hap
      wp_apply (h_NewVersionedSet rc (reconcile S t e.set) e.version e.applied) as %ni #Hni
      · iexact Hrc
      try wp_auto
      wp_apply (wp_mapInsert go.string r R key ni) $$ Hr as Hr
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, key, _
      simp only [named]
      iframe
      isplitr
      · ipureintro; omega
      isplitr
      · ipureintro; exact take_dom_step R keys j key _ Hj Hkey HR
      imodintro
      iintro %k %i %e' ⟨%hk, %he'⟩
      by_cases hkk : key = k
      · subst hkk
        rw [GMap.lookup_insert] at hk; cases hk
        rw [he] at he'; cases he'
        iexact Hni
      · rw [GMap.lookup_insert_ne _ _ hkk] at hk
        iapply HRE $$ %k %i %e'; ipureintro; exact ⟨hk, he'⟩
  iintro HP -
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at HR
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iapply Hclose $$ Hr
  · ipureintro
    refine ⟨reconcileMF_sorted_law_holds S t mf hMs, fun k => ?_⟩
    rw [reconcileMF_get_law_holds, Option.isSome_map]
    have h1 := HR k
    have h2 := Hkset k
    have h3 := hMk k
    cases h : (R !! k).isSome <;> cases h' : (mf.get k).isSome <;> simp_all
  imodintro
  iintro %k %i %e' ⟨%hk, %he'⟩
  rw [reconcileMF_get_law_holds] at he'
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 he'
  iapply HRE $$ %k %i %e; ipureintro; exact ⟨hk, he⟩

end proof

end smd
end EtcdGrove
end Perennial
