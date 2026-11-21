/-
`merge.Updater.Update`: proved over its callees' specs (glue): `reconcileManagedFieldsWithSchemaChanges`
(`mf0`), `update` forced (`afterUpdate`, the comparison), then the manager's own entry (a map read,
`NewSet()` when absent, `Difference`/`Union`, a map write and a delete when empty: `updateResult`
line by line, over `ownMF_access`); the result handed out by `ownMF_persist`.
Lean-first (2026-11-19); proved in the Prove phase (2026-11-21).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__Update
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Difference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__reconcileManagedFieldsWithSchemaChanges
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__update
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofs
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsMF
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

theorem merge.Updater.Update.wp_proof
    (h_NewSet : fieldpath.NewSet.spec (GF := GF))
    (h_NewVersionedSet : fieldpath.NewVersionedSet.spec (GF := GF))
    (h_Set_Difference : fieldpath.Set.Difference.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF))
    (h_Updater_reconcileManagedFieldsWithSchemaChanges : merge.Updater.reconcileManagedFieldsWithSchemaChanges.spec (GF := GF))
    (h_Updater_update : merge.Updater.update.spec (GF := GF)) :
    merge.Updater.Update.spec (GF := GF) :=
    fun u cv rion sc S t lp np live new ver mfm mf mgr => by
  wp_start as ⟨#Hu, #Hcv, #Hl, #Hn, #Hmf, %hsmall⟩
  have hsz : live.size < smdSizeMax ∧ new.size < smdSizeMax ∧
      (mfUnion mf).nodes.card < smdSizeMax := by
    have h1 := hsmall
    simp only [inputsSmall, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
    omega
  wp_auto
  wp_apply (h_Updater_reconcileManagedFieldsWithSchemaChanges u cv _ _ rion sc S t lp live mfm mf)
    as %r0 %err0 ⟨%herr0, Hr0⟩
  · iframe Hu Hcv Hl Hmf; ipureintro; exact hsz.2.2
  subst herr0
  wp_auto
  wp_apply (h_Updater_update u cv rion sc S t lp live np new ver r0 (reconcileMF S t mf) mgr true) $$ [Hr0]
    as %r1 %cp %err1 Hpost
  · iframe Hu Hcv Hl Hn Hr0; ipureintro; exact ⟨hsz.1, hsz.2.1⟩
  icases Hpost with ⟨%h1, Hr0, #Hcmp⟩
  obtain ⟨rfl, rfl⟩ := h1
  wp_auto
  obtain ⟨c, hc⟩ : ∃ c, c = compare S t live new := ⟨_, rfl⟩
  obtain ⟨mf2, hmf2⟩ : ∃ mf2, mf2 = afterUpdate (reconcileMF S t mf) mgr
      (conflictsOf (reconcileMF S t mf) mgr c) c.removed := ⟨_, rfl⟩
  rw [← hc]
  rw [← hmf2]
  have hres : updateResult S t live new ver mf mgr =
      let base := match mf2.get mgr with
        | some e => e.set
        | none => PathSet.empty
      let s := ((base.diff c.removed).union c.modified).union c.added
      if s.IsEmpty then mf2.filter (fun me => me.1 != mgr) else mf2.set mgr ⟨s, ver, false⟩ := by
    subst hc hmf2; rfl
  rw [hres]
  icases (ownMF_access_law_holds r1 _) $$ Hr0 with ⟨%M, HM, %hM, #Hview, Hback⟩
  obtain ⟨hsorted, hdom⟩ := hM
  wp_apply (wp_map_lookup2 go.string fieldpath.VersionedSet.ty r1 M mgr) $$ HM as HM
  try wp_auto
  wp_join iprop(∃ (M1 : GMap GoString GoInterface) (i1 : GoInterface) (v1 : GoString) (a1 : Bool),
      version_ptr ↦ ver ∗ managers_ptr ↦ r1 ∗ manager_ptr ↦ mgr ∗ r1 ↦$ M1 ∗ ⌜M1 !! mgr = some i1 ∧ ∀ k, k ≠ mgr → M1 !! k = M !! k⌝ ∗
      isVSet i1 ⟨match mf2.get mgr with
        | some e => e.set
        | none => PathSet.empty, v1, a1⟩)
    with [HM version managers manager] as ⟨%M1, %i1, %v1, %a1, version, managers, manager, HM, %hM1, #Hi1⟩
  · -- an entry
    have hsome : (M !! mgr).isSome := by simpa using Hif
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
    have hg := hdom mgr
    rw [hi] at hg
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hg.symm
    iexists M, i, e.version, e.applied
    iframe HM version managers manager
    isplitr
    · ipureintro; exact ⟨hi, fun _ _ => rfl⟩
    rw [he]
    iapply Hview; ipureintro; exact ⟨hi, he⟩
  · -- no entry: `NewVersionedSet(NewSet(), version, false)`
    have hnone : M !! mgr = none := by simpa using Hif
    have hget : mf2.get mgr = none := by
      have := hdom mgr; rw [hnone] at this; simpa using this.symm
    ihave Hnil := ownSlice_nil (V := GoSlice) (GF := GF) DFrac.discard
    wp_apply (h_NewSet slice.nil DFrac.discard DFrac.discard [] []) $$ [$Hnil] as %s0 ⟨-, -, Hs0⟩
    · unfold isPathsF; itrivial
    imod ownSet_persist_law_holds _ _ $$ Hs0 with #Hs0
    try wp_auto
    wp_apply (h_NewVersionedSet s0 _ ver false) as %i0 #Hi0
    · iexact Hs0
    try wp_auto
    wp_apply (wp_mapInsert go.string r1 M mgr i0) $$ HM as HM
    try wp_auto
    wp_join_done
    iexists (<[mgr := i0]> M), i0, ver, false
    iframe HM version managers manager
    isplitr
    · ipureintro
      exact ⟨GMap.lookup_insert _ _ _, fun k hk => GMap.lookup_insert_ne _ _ (Ne.symm hk)⟩
    rw [hget, show (PathSet.empty : PathSet) = PathSet.ofList ([] : List Path) from rfl]
    iexact Hi0
  icases (isComparison_open_law_holds cp c).1 $$ Hcmp with ⟨%rr, %rm, %ra, #Hcp, #Hrr, #Hrm, #Hra⟩
  iStructNamed Hcp
  try wp_auto
  wp_apply (wp_map_lookup1 go.string fieldpath.VersionedSet.ty r1 M1 mgr) $$ HM as HM
  rw [hM1.1]
  simp only [Option.getD_some]
  ihave ⟨%iv1, %hiv1⟩ := isVSet_concrete_law_holds _ _ $$ Hi1
  subst hiv1
  wp_auto
  wp_apply (h_versionedSet_Set iv1 _) as %sb #Hsb
  · iexact Hi1
  wp_apply (h_Set_Difference sb rr _ _) as %sd #Hsd
  · iframe Hsb Hrr
  wp_apply (h_Set_Union sd rm _ _) as %su #Hsu
  · iframe Hsd Hrm
  wp_apply (h_Set_Union su ra _ _) as %su2 #Hsu2
  · iframe Hsu Hra
  try wp_auto
  unfold isUpdater
  iStructNamed Hu
  wp_auto
  rw [show (zero_val GoMap) = map.nil from rfl]
  wp_auto
  obtain ⟨s', hs'⟩ : ∃ s', s' = (((match mf2.get mgr with
      | some e => e.set
      | none => PathSet.empty).diff c.removed).union c.modified).union c.added := ⟨_, rfl⟩
  rw [← hs']
  wp_apply (h_NewVersionedSet su2 s' ver false) as %i2 #Hi2
  · iexact Hsu2
  try wp_auto
  wp_apply (wp_mapInsert go.string r1 M1 mgr i2) $$ HM as HM
  try wp_auto
  wp_apply (wp_map_lookup1 go.string fieldpath.VersionedSet.ty r1 _ mgr) $$ HM as HM
  ihave ⟨%iv2, %hiv2⟩ := isVSet_concrete_law_holds _ _ $$ Hi2
  subst hiv2
  try wp_auto
  wp_apply (h_versionedSet_Set iv2 _) as %sb2 #Hsb2
  · iexact Hi2
  wp_apply (h_Set_Empty sb2 s') as %emp %hemp
  · iexact Hsb2
  have hM1ne : ∀ k, k ≠ mgr → M1 !! k = M !! k := hM1.2
  by_cases hE : s'.IsEmpty
  · have : emp = true := hemp.2 hE
    subst this
    simp only [hE, ite_true]
    iapply wp_fupd
    try wp_auto
    wp_apply (wp_mapDelete_underlying (t := fieldpath.ManagedFields.ty) r1 _ mgr) $$ HM as HM
    ihave Hown : ownMF r1 (mf2.filter (fun me => me.1 != mgr)) $$ [HM Hback]
    iapply Hback $$ HM
    · ipureintro
      refine ⟨MF_filter_sorted mf2 _ hsorted, fun k => ?_⟩
      rw [MF_get_filter_ne]
      by_cases hk : k = mgr
      · subst hk; simp
      · rw [GMap.lookup_delete_ne _ (Ne.symm hk), GMap.lookup_insert_ne _ _ (Ne.symm hk), hM1ne k hk]
        simp only [hk, ite_false]; exact hdom k
    · imodintro
      iintro %k %i %e %h
      obtain ⟨hk1, hk2⟩ := h
      rw [MF_get_filter_ne] at hk2
      by_cases hk : k = mgr
      · simp [hk] at hk2
      · rw [GMap.lookup_delete_ne _ (Ne.symm hk), GMap.lookup_insert_ne _ _ (Ne.symm hk), hM1ne k hk] at hk1
        simp only [hk, ite_false] at hk2
        iapply Hview; ipureintro; exact ⟨hk1, hk2⟩
    imod ownMF_persist_law_holds _ _ $$ Hown with #Hmf'
    imodintro
    iapply HΦ
    iframe Hmf'
    ipureintro; exact ⟨rfl, rfl⟩
  · have : emp = false := by cases emp <;> simp_all
    subst this
    simp only [hE, ite_false]
    ihave Hown : ownMF r1 (mf2.set mgr ⟨s', ver, false⟩) $$ [HM Hback]
    iapply Hback $$ HM
    · ipureintro
      refine ⟨MF.set_sorted_law_holds mf2 _ _ hsorted, fun k => ?_⟩
      rw [MF.get_set_law_holds]
      by_cases hk : k = mgr
      · subst hk; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), hM1ne k hk]
        simp only [hk, ite_false]; exact hdom k
    · imodintro
      iintro %k %i %e %h
      obtain ⟨hk1, hk2⟩ := h
      rw [MF.get_set_law_holds] at hk2
      by_cases hk : k = mgr
      · subst hk
        rw [GMap.lookup_insert] at hk1
        simp only [ite_true, Option.some.injEq] at hk2 hk1
        subst hk1 hk2
        iexact Hi2
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), hM1ne k hk] at hk1
        simp only [hk, ite_false] at hk2
        iapply Hview; ipureintro; exact ⟨hk1, hk2⟩
    imod ownMF_persist_law_holds _ _ $$ Hown with #Hmf'
    try wp_auto
    iapply HΦ
    iframe Hmf'
    ipureintro; exact ⟨rfl, rfl⟩

end proof

end smd
end EtcdGrove
end Perennial
