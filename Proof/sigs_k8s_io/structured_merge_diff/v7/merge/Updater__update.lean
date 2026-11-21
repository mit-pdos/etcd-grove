/-
`merge.Updater.update`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `typed.TypedValue.Compare`, `typed.Comparison.FilterFields`,
`fieldpath.versionedSet.Set`, `fieldpath.versionedSet.APIVersion`, `fieldpath.versionedSet.Applied`,
`fieldpath.Set.Union`, `fieldpath.Set.Intersection`, `fieldpath.Set.Difference`,
`fieldpath.Set.Empty`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__update
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Difference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Intersection
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Applied
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.ConflictsFromManagers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.Comparison__ExcludeFields
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.Comparison__FilterFields
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Compare_ptr
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsUpdate
import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA

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

theorem merge.Updater.update.wp_proof
    (h_NewVersionedSet : fieldpath.NewVersionedSet.spec (GF := GF))
    (h_Set_Difference : fieldpath.Set.Difference.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_Intersection : fieldpath.Set.Intersection.spec (GF := GF))
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Applied : fieldpath.versionedSet.Applied.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF))
    (h_ConflictsFromManagers : merge.ConflictsFromManagers.spec (GF := GF))
    (h_Comparison_ExcludeFields : typed.Comparison.ExcludeFields.spec (GF := GF))
    (h_Comparison_FilterFields : typed.Comparison.FilterFields.spec (GF := GF))
    (h_TypedValue_Compare_ptr : typed.TypedValue.Compare_ptr.spec (GF := GF)) :
    merge.Updater.update.spec (GF := GF) :=
    fun u cv rion sc S t op old np new ver mfm mf wf force => by
  wp_start as ⟨#Hu, #Hcv, #Hop, #Hnp, Hmf, %hsz⟩
  unfold isUpdater isIdentityConverter
  icases Hcv with ⟨%T, %cvv, %hcv, #HConv, #HMiss⟩
  subst hcv
  iStructNamed Hu
  ihave ⟨%M, HM, %hM, #HE, Hclose⟩ := ownMF_access_law_holds mfm mf $$ Hmf
  obtain ⟨hMs, hMk⟩ := hM
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %cm Hcm
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %rm Hrm
  try wp_auto
  wp_apply (h_TypedValue_Compare_ptr op np sc S t old new) as %c %cerr ⟨%hcerr, Hc⟩
  · iframe Hop Hnp; ipureintro; exact hsz
  subst hcerr
  ihave #Hc := isComparison_persistent_law_holds _ _ $$ Hc
  try wp_auto
  rw [show (zero_val GoMap : GoMap) = map.nil from rfl]
  try wp_auto
  wp_apply (h_Comparison_FilterFields c (compare S t old new) _)
  · iframe Hc; ipureintro; rfl
  iintro -
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %vm Hvm
  try wp_auto
  wp_apply (wp_mapInsert _ vm ∅ ver c) $$ Hvm as Hvm
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (j : Int) => iprop(∃ (CM RM : GMap GoString GoInterface)
      (VM : GMap GoString Loc) (y : GoInterface) (x : GoString),
      "%Hj" ∷ ⌜0 ≤ j⌝ ∗
      "%HCM" ∷ ⌜∀ k, (CM !! k).isSome = true ↔
        (k ∈ keys.take j.toNat ∧ ((conflictsMF mf wf (compare S t old new)).get k).isSome = true)⌝ ∗
      "#HCE" ∷ □ (∀ k i e, ⌜CM !! k = some i ∧ (conflictsMF mf wf (compare S t old new)).get k = some e⌝ -∗
        isVSet i e) ∗
      "%HRM" ∷ ⌜∀ k, (RM !! k).isSome = true ↔
        (k ∈ keys.take j.toNat ∧ k ≠ wf ∧ ¬ (compare S t old new).removed.IsEmpty)⌝ ∗
      "#HRE" ∷ □ (∀ k i e, ⌜RM !! k = some i ∧ mf.get k = some e⌝ -∗
        isVSet i ⟨(compare S t old new).removed, e.version, false⟩) ∗
      "#HVE" ∷ □ (∀ v p, ⌜VM !! v = some p⌝ -∗ isComparison p (compare S t old new)) ∗
      "Hcm" ∷ cm ↦$ CM ∗
      "Hrm" ∷ rm ↦$ RM ∗
      "Hvm" ∷ vm ↦$ VM ∗
      "versions" ∷ versions_ptr ↦ vm ∗
      "managerSet" ∷ managerSet_ptr ↦ y ∗
      "manager" ∷ manager_ptr ↦ x ∗
      "workflow" ∷ workflow_ptr ↦ wf ∗
      "oldObject" ∷ oldObject_ptr ↦ op ∗
      "newObject" ∷ newObject_ptr ↦ np ∗
      "s" ∷ s_ptr ↦ u ∗
      "conflicts" ∷ conflicts_ptr ↦ cm ∗
      "removed" ∷ removed_ptr ↦ rm)) $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hcm Hrm Hvm versions managerSet manager workflow oldObject newObject s conflicts removed]
  · iexists ∅, ∅, _, _, _
    simp only [named]
    iframe
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; intro k; simp
    isplitr
    · imodintro; iintro %k %i %e ⟨%hk, -⟩; simp at hk
    isplitr
    · ipureintro; intro k; simp
    isplitr
    · imodintro; iintro %k %i %e ⟨%hk, -⟩; simp at hk
    imodintro
    iintro %v %p %hv
    by_cases hvv : ver = v
    · subst hvv; rw [GMap.lookup_insert] at hv; cases hv; iexact Hc
    · rw [GMap.lookup_insert_ne _ _ hvv] at hv; simp at hv
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
    have hnotin := MUpd.key_notin_take keys j key Hknodup Hkey
    have htk := MUpd.mem_take_succ keys j key Hj Hkey
    by_cases hkw : key = wf
    · rw [decide_eq_true hkw]
      wp_auto
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists CM, RM, VM, _, _
      simp only [named]
      iframe
      isplitr
      · ipureintro; omega
      isplitr
      · ipureintro
        intro k
        rw [HCM k, htk k]
        by_cases hk : k = key
        · subst hk
          rw [MUpd.conflictsMF_get mf wf _ hMs, he]
          simp [hkw]
        · simp [hk]
      isplitr
      · iexact HCE
      isplitr
      · ipureintro
        intro k
        rw [HRM k, htk k]
        by_cases hk : k = key
        · subst hk; simp [hkw]
        · simp [hk]
      isplitr
      · iexact HRE
      iexact HVE
    rw [decide_eq_false hkw]
    wp_auto
    wp_apply (h_versionedSet_APIVersion vv e) as %ev %hev
    · iexact Hve
    subst hev
    wp_apply (wp_map_lookup2 _ _ vm VM e.version) $$ Hvm as Hvm
    try wp_auto
    wp_join iprop(∃ (VM' : GMap GoString Loc) (p : Loc),
        "Hvm" ∷ vm ↦$ VM' ∗
        "#HVE" ∷ □ (∀ v p, ⌜VM' !! v = some p⌝ -∗ isComparison p (compare S t old new)) ∗
        "compare" ∷ compare_ptr ↦ p ∗
        "#Hp" ∷ isComparison p (compare S t old new) ∗
        "oldObject" ∷ oldObject_ptr ↦ op ∗
        "newObject" ∷ newObject_ptr ↦ np ∗
        "s" ∷ s_ptr ↦ u ∗
        "managerSet" ∷ managerSet_ptr ↦ interface.mkOk fieldpath.versionedSet.ty #vv ∗
        "versions" ∷ versions_ptr ↦ vm)
      with [Hvm compare oldObject newObject s managerSet versions] as ⟨%VM', %p, Hvm, #HVE', compare, #Hp,
        oldObject, newObject, s, managerSet, versions⟩
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 Hif
      rw [hp, Option.getD_some]
      iexists VM, p
      simp only [named]
      iframe
      isplitr
      · iexact HVE
      iapply HVE $$ %_ %_ %hp
    · wp_apply (h_versionedSet_APIVersion vv e) as %ev %hev
      · iexact Hve
      subst hev
      try wp_auto
      wp_bind (App (App (Val #(methods T go!"Convert" cvv)) (Val #op)) (Val #e.version))
      iapply HConv
      inext
      try wp_auto
      wp_apply (h_versionedSet_APIVersion vv e) as %ev %hev
      · iexact Hve
      subst hev
      try wp_auto
      wp_bind (App (App (Val #(methods T go!"Convert" cvv)) (Val #np)) (Val #e.version))
      iapply HConv
      inext
      try wp_auto
      wp_apply (h_TypedValue_Compare_ptr op np sc S t old new) as %c2 %cerr2 ⟨%hcerr2, Hc2⟩
      · iframe Hop Hnp; ipureintro; exact hsz
      subst hcerr2
      ihave #Hc2 := isComparison_persistent_law_holds _ _ $$ Hc2
      try wp_auto
      wp_apply (h_versionedSet_APIVersion vv e) as %ev %hev
      · iexact Hve
      subst hev
      try wp_auto
      try wp_auto
      wp_apply (h_Comparison_FilterFields c2 (compare S t old new) _)
      · iframe Hc2; ipureintro; rfl
      iintro -
      try wp_auto
      wp_apply (h_versionedSet_APIVersion vv e) as %ev %hev
      · iexact Hve
      subst hev
      try wp_auto
      wp_apply (wp_mapInsert _ vm VM e.version c2) $$ Hvm as Hvm
      wp_join_done
      iexists _, c2
      simp only [named]
      iframe
      imodintro
      iintro %v %p %hv
      by_cases hvv : e.version = v
      · subst hvv; rw [GMap.lookup_insert] at hv; cases hv; iexact Hc2
      · rw [GMap.lookup_insert_ne _ _ hvv] at hv; iapply HVE $$ %_ %_ %hv
    ihave ⟨%r0, %m0, %a0, #Hpf, #Hr0, #Hm0, #Ha0⟩ := (isComparison_open_law_holds p _).1 $$ Hp
    iStructNamed Hpf
    try wp_auto
    wp_apply (h_Set_Union m0 a0 _ _) as %un #Hun
    · isplitr
      · iexact Hm0
      · iexact Ha0
    wp_apply (h_versionedSet_Set vv e) as %sp #Hsp
    · iexact Hve
    wp_apply (h_Set_Intersection sp un _ _) as %cs #Hcs
    · isplitr
      · iexact Hsp
      · iexact Hun
    try wp_auto
    have hcget := MUpd.conflictsMF_get mf wf (compare S t old new) hMs key
    rw [he] at hcget
    simp only [Option.bind_some, hkw, ite_false] at hcget
    wp_apply (h_Set_Empty cs _) as %b %hb
    · iexact Hcs
    try wp_auto
    wp_join iprop(∃ (CM' : GMap GoString GoInterface),
        "Hcm" ∷ cm ↦$ CM' ∗
        "%HCM'" ∷ ⌜∀ k, (CM' !! k).isSome = true ↔
          (k ∈ keys.take (j + 1).toNat ∧ ((conflictsMF mf wf (compare S t old new)).get k).isSome = true)⌝ ∗
        "#HCE'" ∷ □ (∀ k i e, ⌜CM' !! k = some i ∧ (conflictsMF mf wf (compare S t old new)).get k = some e⌝ -∗
          isVSet i e) ∗
        "conflicts" ∷ conflicts_ptr ↦ cm ∗
        "manager" ∷ manager_ptr ↦ key ∗
        "conflictSet" ∷ conflictSet_ptr ↦ cs ∗
        "managerSet" ∷ managerSet_ptr ↦ interface.mkOk fieldpath.versionedSet.ty #vv)
      at (if: _ then _ else _)
      with [Hcm conflicts manager managerSet conflictSet]
      as ⟨%CM', Hcm, %HCM', #HCE', conflicts, manager, conflictSet, managerSet⟩
    cases b
    · -- a conflict: the entry
      have hne : ¬ (e.set.inter ((compare S t old new).modified.union (compare S t old new).added)).IsEmpty := by
        intro h; have := hb.2 h; cases this
      rw [if_neg hne] at hcget
      simp only [Bool.not_false]
      wp_auto
      wp_apply (h_versionedSet_APIVersion vv e) as %ev %hev
      · iexact Hve
      subst hev
      wp_apply (h_NewVersionedSet cs _ e.version false) as %ni #Hni
      · iexact Hcs
      try wp_auto
      wp_apply (wp_mapInsert _ cm CM key ni) $$ Hcm as Hcm
      wp_join_done
      iexists _
      simp only [named]
      iframe
      isplitr
      · ipureintro
        intro k
        rw [htk k]
        by_cases hk : k = key
        · subst hk; simp [hcget]
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), HCM k]; simp [hk]
      imodintro
      iintro %k %i %e' ⟨%hk, %he'⟩
      by_cases hkk : key = k
      · subst hkk
        rw [GMap.lookup_insert] at hk; cases hk
        rw [hcget] at he'; cases he'
        iexact Hni
      · rw [GMap.lookup_insert_ne _ _ hkk] at hk
        iapply HCE $$ %k %i %e'; ipureintro; exact ⟨hk, he'⟩
    · -- no conflict
      have hem : (e.set.inter ((compare S t old new).modified.union (compare S t old new).added)).IsEmpty :=
        hb.1 rfl
      rw [if_pos hem] at hcget
      simp only [Bool.not_true]
      wp_auto
      wp_join_done
      iexists CM
      simp only [named]
      iframe
      isplitr
      · ipureintro
        intro k
        rw [htk k, HCM k]
        by_cases hk : k = key
        · subst hk; simp [hcget, hnotin]
        · simp [hk]
      iexact HCE
    wp_apply (h_Set_Empty r0 _) as %b2 %hb2
    · iexact Hr0
    wp_join iprop(∃ (RM' : GMap GoString GoInterface),
        "Hrm" ∷ rm ↦$ RM' ∗
        "%HRM'" ∷ ⌜∀ k, (RM' !! k).isSome = true ↔
          (k ∈ keys.take (j + 1).toNat ∧ k ≠ wf ∧ ¬ (compare S t old new).removed.IsEmpty)⌝ ∗
        "#HRE'" ∷ □ (∀ k i e, ⌜RM' !! k = some i ∧ mf.get k = some e⌝ -∗
          isVSet i ⟨(compare S t old new).removed, e.version, false⟩) ∗
        "removed" ∷ removed_ptr ↦ rm ∗
        "manager" ∷ manager_ptr ↦ key ∗
        "compare" ∷ compare_ptr ↦ p ∗
        "managerSet" ∷ managerSet_ptr ↦ interface.mkOk fieldpath.versionedSet.ty #vv)
      at (if: _ then _ else _)
      with [Hrm removed manager managerSet compare]
      as ⟨%RM', Hrm, %HRM', #HRE', removed, manager, compare, managerSet⟩
    cases b2
    · have hne : ¬ (compare S t old new).removed.IsEmpty := by
        intro h; have := hb2.2 h; cases this
      simp only [Bool.not_false]
      wp_auto
      wp_apply (h_versionedSet_APIVersion vv e) as %ev %hev
      · iexact Hve
      subst hev
      wp_apply (h_NewVersionedSet r0 _ e.version false) as %ni #Hni
      · iexact Hr0
      try wp_auto
      wp_apply (wp_mapInsert _ rm RM key ni) $$ Hrm as Hrm
      wp_join_done
      iexists _
      simp only [named]
      iframe
      isplitr
      · ipureintro
        intro k
        rw [htk k]
        by_cases hk : k = key
        · subst hk; simp [hkw, hne]
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), HRM k]; simp [hk]
      imodintro
      iintro %k %i %e' ⟨%hk, %he'⟩
      by_cases hkk : key = k
      · subst hkk
        rw [GMap.lookup_insert] at hk; cases hk
        rw [he] at he'; cases he'
        iexact Hni
      · rw [GMap.lookup_insert_ne _ _ hkk] at hk
        iapply HRE $$ %k %i %e'; ipureintro; exact ⟨hk, he'⟩
    · have hem : (compare S t old new).removed.IsEmpty := hb2.1 rfl
      simp only [Bool.not_true]
      wp_auto
      wp_join_done
      iexists RM
      simp only [named]
      iframe
      isplitr
      · ipureintro
        intro k
        rw [htk k, HRM k]
        by_cases hk : k = key
        · subst hk; simp [hem, hnotin]
        · simp [hk]
      iexact HRE
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists CM', RM', VM', _, _
    simp only [named]
    iframe
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; exact HCM'
    isplitr
    · iexact HCE'
    isplitr
    · ipureintro; exact HRM'
    isplitr
    · iexact HRE'
    iexact HVE'
  iintro HP HM
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at HCM HRM
  have hkmf : ∀ k, k ∈ keys ↔ (mf.get k).isSome = true := fun k => by rw [Hkset k, hMk k]
  have HCM2 : ∀ k, (CM !! k).isSome = ((conflictsMF mf wf (compare S t old new)).get k).isSome := by
    intro k
    have h := HCM k
    rw [MUpd.conflictsMF_get mf wf _ hMs k] at h ⊢
    rw [hkmf k] at h
    cases hg : mf.get k <;> cases hc : (CM !! k).isSome <;> simp_all
  have HRM2 : ∀ k, (RM !! k).isSome = true ↔
      ((mf.get k).isSome = true ∧ k ≠ wf ∧ ¬ (compare S t old new).removed.IsEmpty) := by
    intro k; rw [HRM k, hkmf k]
  have hCsorted := MUpd.conflictsMF_sorted_law_holds mf wf (compare S t old new) hMs
  have hCnil := MUpd.conflictsMF_nil_iff_law_holds mf wf (compare S t old new)
  have hsz0 : GMap.size CM = 0 ↔ conflictsMF mf wf (compare S t old new) = [] := by
    rw [GMap.map_size_empty_iff]
    constructor
    · intro h
      cases hc : conflictsMF mf wf (compare S t old new) with
      | nil => rfl
      | cons me rest =>
        exfalso
        have h1 := HCM2 me.1
        rw [h, hc] at h1
        simp [MF.get, lookupKV] at h1
    · intro h
      apply (GMap.lookup_empty_iff CM).1
      intro k
      have h1 := HCM2 k
      rw [h] at h1
      simpa [MF.get, lookupKV] using h1
  wp_auto
  wp_join (v := #(decide (force = false ∧ conflictsMF mf wf (compare S t old new) ≠ [])))
      iprop("Hcm" ∷ cm ↦$ CM ∗ "conflicts" ∷ conflicts_ptr ↦ cm)
      at (if: #!force then _ else #false) with [Hcm conflicts] as ⟨Hcm, conflicts⟩
  · cases force
    · simp only [Bool.not_false]
      wp_auto
      wp_apply (wp_map_len_lt (t := fieldpath.ManagedFields.ty) cm CM) $$ Hcm as ⟨Hcm, %hlt⟩
      try wp_auto
      iframe
      ipureintro
      have : (W64 (GMap.size CM) = W64 0) ↔ conflictsMF mf wf (compare S t old new) = [] := by
        rw [← hsz0]
        constructor
        · intro h; have := congrArg (fun w : w64 => w.toNat) h; simp at this; omega
        · intro h; rw [h]; rfl
      by_cases hc : conflictsMF mf wf (compare S t old new) = []
      · simp [hc, this.2 hc]
      · have : ¬ W64 (GMap.size CM) = W64 0 := fun h => hc (this.1 h)
        rw [decide_eq_false this]; simp [hc]
    · simp only [Bool.not_true]
      try wp_auto
      iframe
      ipureintro
      simp
  by_cases hcf : force = false ∧ conflictsMF mf wf (compare S t old new) ≠ []
  · rw [decide_eq_true hcf]
    wp_auto
    imod (ownMap_persist _ _ _) $$ Hcm with #Hcm
    ihave #HCmf := isMF_of_map cm CM _ hCsorted HCM2 $$ [Hcm HCE]
    · iframe Hcm; iexact HCE
    wp_apply (h_ConflictsFromManagers cm _) as %sl ⟨%l, ⟨%hlnd, %hlset⟩, #Hl⟩
    · iexact HCmf
    try wp_auto
    iapply HΦ
    have hcond : (!force && !(conflictsOf mf wf (compare S t old new)).isEmpty) = true := by
      obtain ⟨h1, h2⟩ := hcf
      subst h1
      simp only [Bool.not_false, Bool.true_and, Bool.not_eq_true']
      cases h : (conflictsOf mf wf (compare S t old new)).isEmpty
      · rfl
      · exact absurd (hCnil.2 h) h2
    rw [if_pos hcond]
    ihave HMF := Hclose $$ %M %mf HM %(⟨hMs, hMk⟩) HE
    iframe HMF
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists sl, l
    iframe Hl
    ipureintro
    exact ⟨rfl, hlnd, by rw [hlset, MUpd.mfPairs_conflictsMF_law_holds]⟩
  rw [decide_eq_false hcf]
  wp_auto
  sorry

end proof

end smd
end EtcdGrove
end Perennial
