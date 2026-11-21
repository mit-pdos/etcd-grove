/-
`merge.Updater.Apply`: proved over its callees' specs (glue, `applyResult` line by line):
`reconcileManagedFieldsWithSchemaChanges` (`mf0`), `Merge`, the applier's last entry read
(`isVSetOpt`), `ToFieldSet`, its new entry written (`mf1`, over `ownMF_access`), `prune`, `update`
(the conflicts, with a fresh empty map, or the new managers), then the no-op check
(`EqualsUsing`). The pure premises of `prune` come from `merge/LawProofsGlue.lean`.
`prune`'s union bound `(mfUnion mf1).nodes.card < smdSizeMax` from `inputsSmall`'s combined bound
(`Glue.apply_union_small`: the old union's nodes and the configuration's field set's, at most its
size).
Lean-first (2026-11-19); proved in the Prove phase (2026-11-21).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__Apply
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__prune
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__reconcileManagedFieldsWithSchemaChanges
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__update
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__AsValue_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Merge_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__ToFieldSet_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsGlue
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

theorem merge.Updater.Apply.wp_proof
    (h_NewVersionedSet : fieldpath.NewVersionedSet.spec (GF := GF))
    (h_Updater_prune : merge.Updater.prune.spec (GF := GF))
    (h_Updater_reconcileManagedFieldsWithSchemaChanges : merge.Updater.reconcileManagedFieldsWithSchemaChanges.spec (GF := GF))
    (h_Updater_update : merge.Updater.update.spec (GF := GF))
    (h_TypedValue_AsValue_ptr : typed.TypedValue.AsValue_ptr.spec (GF := GF))
    (h_TypedValue_Merge_ptr : typed.TypedValue.Merge_ptr.spec (GF := GF))
    (h_TypedValue_ToFieldSet_ptr : typed.TypedValue.ToFieldSet_ptr.spec (GF := GF))
    (h_EqualsUsing : value.EqualsUsing.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF)) :
    merge.Updater.Apply.spec (GF := GF) :=
    fun u cv rion sc S t lp cp live config ver mfm mf mgr force => by
  wp_start as ⟨#Hu, #Hcv, #Hl, #Hc, #Hmf, %hpre, %hsmall⟩
  have hsz : live.size + config.size < smdSizeMax ∧ (mfUnion mf).nodes.card < smdSizeMax := by
    have h1 := hsmall
    simp only [inputsSmall, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
    omega
  have hunion := Glue.apply_union_small S t live config mf mgr ver hsmall
  ihave ⟨#Hsc, %hwf⟩ := isTV_schema_law_holds _ _ _ _ _ $$ Hl
  ihave %hcl := isTV_conforms_law_holds _ _ _ _ _ $$ Hl
  ihave %hcc := isTV_conforms_law_holds _ _ _ _ _ $$ Hc
  wp_auto
  wp_apply (h_Updater_reconcileManagedFieldsWithSchemaChanges u cv _ _ rion sc S t lp live mfm mf)
    as %r0 %err0 ⟨%herr0, Hr0⟩
  · iframe Hu Hcv Hl Hmf; ipureintro; exact hsz.2
  subst herr0
  wp_auto
  wp_apply (h_TypedValue_Merge_ptr lp cp sc S t live config) as %mp %errm ⟨%herrm, #Hm⟩
  · iframe Hl Hc
  subst herrm
  wp_auto
  obtain ⟨mf0, hmf0⟩ : ∃ mf0, mf0 = reconcileMF S t mf := ⟨_, rfl⟩
  rw [← hmf0]
  icases (ownMF_access_law_holds r0 mf0) $$ Hr0 with ⟨%M, HM, %hM, #Hview, Hback⟩
  obtain ⟨hsorted, hdom⟩ := hM
  wp_apply (wp_map_lookup1 go.string fieldpath.VersionedSet.ty r0 M mgr) $$ HM as HM
  ihave Hls : isVSetOpt ((M !! mgr).getD (zero_val GoInterface)) (mf0.get mgr) $$ []
  · cases hg : mf0.get mgr with
    | none =>
      have hM : M !! mgr = none := by
        have := hdom mgr; rw [hg] at this; simpa using this
      rw [hM]; unfold isVSetOpt; ipureintro; rfl
    | some e =>
      have hs : (M !! mgr).isSome := by rw [hdom, hg]; rfl
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
      rw [hi]; unfold isVSetOpt
      iapply Hview; ipureintro; exact ⟨hi, hg⟩
  try wp_auto
  wp_apply (h_TypedValue_ToFieldSet_ptr cp sc S t config) as %fs %errf ⟨%herrf, Hfs⟩
  · iframe Hc; ipureintro; omega
  subst herrf
  imod ownSet_persist_law_holds _ _ $$ Hfs with #Hfs
  try wp_auto
  unfold isUpdater
  iStructNamed Hu
  wp_auto
  rw [show (zero_val GoMap) = map.nil from rfl]
  wp_auto
  wp_apply (h_NewVersionedSet fs (fieldSet S t config) ver true) as %i1 #Hi1
  · iexact Hfs
  try wp_auto
  wp_apply (wp_mapInsert go.string r0 M mgr i1) $$ HM as HM
  obtain ⟨mf1, hmf1⟩ : ∃ mf1, mf1 = mf0.set mgr ⟨fieldSet S t config, ver, true⟩ := ⟨_, rfl⟩
  ihave Hr1 : ownMF r0 mf1 $$ [HM Hback]
  · iapply Hback $$ HM
    · ipureintro
      refine ⟨hmf1 ▸ MF.set_sorted_law_holds mf0 _ _ hsorted, fun k => ?_⟩
      rw [hmf1, MF.get_set_law_holds]
      by_cases hk : k = mgr
      · subst hk; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]
        simp only [hk, ite_false]; exact hdom k
    · imodintro
      iintro %k %i %e %h
      obtain ⟨hk1, hk2⟩ := h
      rw [hmf1, MF.get_set_law_holds] at hk2
      by_cases hk : k = mgr
      · subst hk
        rw [GMap.lookup_insert] at hk1
        simp only [ite_true, Option.some.injEq] at hk2 hk1
        subst hk1 hk2
        iexact Hi1
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)] at hk1
        simp only [hk, ite_false] at hk2
        iapply Hview; ipureintro; exact ⟨hk1, hk2⟩
  try wp_auto
  have hmsz : (merge S t live config).size < smdSizeMax := by
    have := Glue.merge_size_conf S t live config hwf hcl hcc
    omega
  have hents := Glue.apply_mf1_entries S t config ver mf mgr hwf hcc hpre
  rw [← hmf0, ← hmf1] at hents
  have hlast := Glue.apply_last S t ver mf mgr hwf hpre hsz.2
  rw [← hmf0] at hlast
  wp_apply (h_Updater_prune u cv map.nil map.nil rion sc S t mp (merge S t live config)
      r0 mf1 mgr ((M !! mgr).getD (zero_val GoInterface)) (mf0.get mgr) ver) $$ [Hr1 Hls]
    as %np %errp ⟨%herrp, Hr1, #Hnp⟩
  · iframe Hm Hr1 Hls Hcv
    isplitr
    · unfold isUpdater; iexact Hu
    isplitr
    · ipureintro
      refine ⟨by rw [hmf1, MF.get_set_law_holds]; simp, fun m e h => (hents m e h).1,
        fun L h => (hlast L h).1⟩
    · ipureintro
      refine ⟨fun m e h => (hents m e h).2, fun L h => (hlast L h).2, hmsz, ?_⟩
      rw [hmf1, hmf0]; exact hunion
  subst herrp
  try wp_auto
  obtain ⟨new, hnew⟩ : ∃ new, new = prune S t (merge S t live config) mf1 (mf0.get mgr) := ⟨_, rfl⟩
  rw [← hnew]
  have hnsz : new.size < smdSizeMax := by
    have := Glue.prune_size_le S t (merge S t live config) mf1 (mf0.get mgr)
    rw [← hnew] at this; omega
  obtain ⟨c, hc⟩ : ∃ c, c = compare S t live new := ⟨_, rfl⟩
  have hres : applyResult S t rion live config ver mf mgr force =
      if !force && !(conflictsOf mf1 mgr c).isEmpty then .conflicts (conflictsOf mf1 mgr c)
      else .ok (if !rion && decide (new = live) then none else some new)
        (afterUpdate mf1 mgr (conflictsOf mf1 mgr c) c.removed) := by
    subst hc hnew hmf1 hmf0; rfl
  rw [hres]
  wp_apply (h_Updater_update u cv rion sc S t lp live np new ver r0 mf1 mgr force) $$ [Hr1]
    as %r2 %cmp %err2 Hpost
  · iframe Hl Hnp Hr1 Hcv
    isplitr
    · unfold isUpdater; rw [show (zero_val GoMap) = map.nil from rfl]; iexact Hu
    ipureintro; exact ⟨by omega, hnsz⟩
  rw [← hc]
  by_cases hcf : (!force && !(conflictsOf mf1 mgr c).isEmpty) = true
  · simp only [hcf, ite_true]
    icases Hpost with ⟨%hr2, Hr1, %cs, %l, %hcs, #Hcs⟩
    obtain ⟨rfl, rfl⟩ := hr2
    obtain ⟨rfl, hnd, hl⟩ := hcs
    iapply wp_fupd
    wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string fieldpath.VersionedSet.ty)
      as %m0 Hm0
    ihave Hown := ownMF_empty_law_holds m0 $$ Hm0
    imod ownMF_persist_law_holds _ _ $$ Hown with #Hmf0
    try wp_auto
    imodintro
    iapply HΦ
    iframe Hmf0
    isplitr
    · ipureintro; rfl
    iexists cs, l
    iframe Hcs
    ipureintro; exact ⟨rfl, hnd, hl⟩
  · simp only [hcf, ite_false, Bool.false_eq_true]
    icases Hpost with ⟨%hr2, Hr2, #Hcmp⟩
    obtain ⟨rfl, rfl⟩ := hr2
    imod ownMF_persist_law_holds _ _ $$ Hr2 with #Hmf2
    wp_auto
    cases rion with
    | true =>
      wp_auto
      iapply HΦ
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
      iframe Hmf2 Hnp
    | false =>
      wp_auto
      wp_apply h_NewFreelistAllocator as %al Hal
      wp_apply (h_TypedValue_AsValue_ptr lp sc S t live) as %lv #Hlv
      · iexact Hl
      wp_apply (h_TypedValue_AsValue_ptr np sc S t new) as %nv #Hnv
      · iexact Hnp
      wp_apply (h_EqualsUsing al lv nv DFrac.discard DFrac.discard live new) $$ [Hal]
        as %b ⟨-, -, -, %hb⟩
      · iframe Hal Hlv Hnv
      by_cases heq : new = live
      · have : b = true := hb.2 heq.symm
        subst this
        wp_auto
        iapply HΦ
        simp only [Bool.not_false, heq, _root_.decide_true, Bool.and_self, ite_true]
        iframe Hmf2
      · have : b = false := by
          cases b
          · rfl
          · exact absurd (hb.1 rfl).symm heq
        subst this
        wp_auto
        iapply HΦ
        simp only [Bool.not_false, heq, _root_.decide_false, Bool.and_false, Bool.false_eq_true, ite_false]
        iframe Hmf2 Hnp

end proof

end smd
end EtcdGrove
end Perennial
