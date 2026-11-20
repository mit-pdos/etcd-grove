/-
`merge.Updater.prune`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `fieldpath.versionedSet.Set`, `fieldpath.versionedSet.APIVersion`,
`fieldpath.Set.Empty`, `typed.TypedValue.Schema`, `typed.TypedValue.TypeRef`,
`fieldpath.Set.EnsureNamedFieldsAreMembers`, `typed.TypedValue.RemoveItems`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__prune
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackDanglingItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackOwnedItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__RemoveItems_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Schema_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__TypeRef_ptr
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofs
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsMF

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

theorem merge.Updater.prune.wp_proof
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_EnsureNamedFieldsAreMembers : fieldpath.Set.EnsureNamedFieldsAreMembers.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF))
    (h_Updater_addBackDanglingItems : merge.Updater.addBackDanglingItems.spec (GF := GF))
    (h_Updater_addBackOwnedItems : merge.Updater.addBackOwnedItems.spec (GF := GF))
    (h_TypedValue_RemoveItems_ptr : typed.TypedValue.RemoveItems_ptr.spec (GF := GF))
    (h_TypedValue_Schema_ptr : typed.TypedValue.Schema_ptr.spec (GF := GF))
    (h_TypedValue_TypeRef_ptr : typed.TypedValue.TypeRef_ptr.spec (GF := GF)) :
    merge.Updater.prune.spec (GF := GF) :=
    fun u cv igf igfl rion sc S t mp merged mfm mf mgr ls last ver => by
  wp_start as ⟨#Hu, #Hcv, #Hm, Hmf, Hls, %hv, %hk⟩
  obtain ⟨hmgr, hver, hlver⟩ := hv
  obtain ⟨hkmf, hklast, hms, hunion⟩ := hk
  unfold isUpdater isIdentityConverter
  icases Hcv with ⟨%T, %cvv, %hcv, #HConv, #HMiss⟩
  subst hcv
  iStructNamed Hu
  cases last with
  | none =>
    unfold isVSetOpt
    icases Hls with %hls
    subst hls
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iframe Hmf
    simp only [prune]
    iexact Hm
  | some L =>
    unfold isVSetOpt
    ihave #Hls := isVSet_persistent_law_holds _ _ $$ Hls
    ihave ⟨%lv, %hlv⟩ := isVSet_concrete_law_holds _ _ $$ Hls
    subst hlv
    ihave ⟨#Hsc, %hwf⟩ := isTV_schema_law_holds _ _ _ _ _ $$ Hm
    ihave %hconf := isTV_conforms_law_holds _ _ _ _ _ $$ Hm
    have hpc := prune_conforms_law_holds S t merged mf L hwf hconf hkmf (hklast L rfl).1
    have hLv := hlver L rfl
    have hmfne : mf ≠ [] := by
      intro h; subst h; simp [MF.get, lookupKV] at hmgr
    wp_auto
    wp_apply (h_versionedSet_Set lv L) as %ls1 #Hls1
    · iexact Hls
    wp_apply (h_Set_Empty ls1 L.set) as %e %he
    · iexact Hls1
    by_cases hemp : L.set.IsEmpty
    · have : e = true := he.2 hemp
      subst this
      wp_auto
      iapply HΦ
      isplitr
      · ipureintro; rfl
      iframe Hmf
      simp only [prune, hemp, ite_true]
      iexact Hm
    have : e = false := by cases e <;> simp_all
    subst this
    obtain ⟨hc0, hc1, hc2⟩ := hpc
    wp_auto
    wp_apply (h_versionedSet_APIVersion lv L) as %v %hv
    · iexact Hls
    subst hv
    wp_bind (App (App (Val #(methods T go!"Convert" cvv)) (Val #mp)) (Val #L.version))
    iapply HConv
    inext
    wp_auto
    wp_apply (h_TypedValue_Schema_ptr mp sc S t merged)
    · iexact Hm
    wp_apply (h_TypedValue_TypeRef_ptr mp sc S t merged) as %tr #Htr
    · iexact Hm
    try wp_auto
    ihave #Htro := (isTypeRefOpt_some_law_holds tr t).2 $$ Htr
    wp_apply (h_versionedSet_Set lv L) as %ls2 #Hls2
    · iexact Hls
    ihave %hne := isSet_ne_law_holds _ _ $$ Hls2
    wp_apply (h_Set_EnsureNamedFieldsAreMembers ls2 _ sc S tr (some t)) as %e0 #He0
    · iframe Hls2 Hsc Htro; ipureintro; exact ⟨hwf, nodes_cardLt _ hne (hklast L rfl).2⟩
    try wp_auto
    wp_apply (h_TypedValue_RemoveItems_ptr mp e0 sc S t merged _) as %p0 #Hp0
    · iframe Hm He0; ipureintro; exact hc0
    wp_auto
    have hs0 : (removeItems S t merged (ensureNamedOpt S (some t) L.set)).size ≤ merged.size :=
      removeItems_size_law_holds S t merged _
    have hs1 : (addBackOwnedMF S t merged (removeItems S t merged (ensureNamedOpt S (some t) L.set)) mf).size ≤ merged.size := by
      cases mf with
      | nil => exact absurd rfl hmfne
      | cons _ _ => exact removeItems_size_law_holds S t merged _
    wp_apply (h_Updater_addBackOwnedItems u (interface.mkOk T cvv) igf igfl rion sc S t mp merged p0 _ L.version mfm mf mgr) $$ [Hmf] as %p1 %err1 ⟨%herr1, Hmf, #Hp1⟩
    · iframe Hmf Hm Hp0
      isplitr
      · unfold isUpdater; iexact Hu
      isplitr
      · unfold isIdentityConverter
        iexists T, cvv
        isplitr
        · ipureintro; rfl
        iframe HConv HMiss
      isplitr
      · ipureintro; intro m e h; rw [hver m e h, hLv]
      ipureintro
      refine ⟨hms, by omega, hunion, hc1⟩
    subst herr1
    wp_auto
    wp_apply (h_Updater_addBackDanglingItems u (interface.mkOk T cvv) igf igfl rion sc S t mp merged p1 _ _ L) as %p2 %err2 ⟨%herr2, #Hp2⟩
    · iframe Hm Hp1
      isplitr
      · unfold isUpdater; iexact Hu
      isplitr
      · unfold isIdentityConverter
        iexists T, cvv
        isplitr
        · ipureintro; rfl
        iframe HConv HMiss
      isplitr
      · iexact Hls
      ipureintro
      refine ⟨hms, by omega, (hklast L rfl).2, hc2⟩
    subst herr2
    wp_auto
    icases (ownMF_access_law_holds mfm mf) $$ Hmf with ⟨%M, HM, %hM, #Hview, Hback⟩
    obtain ⟨hsorted, hdom⟩ := hM
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hmgr
    have hMi : (M !! mgr).isSome := by rw [hdom]; exact hmgr
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hMi
    wp_apply (wp_map_lookup1 go.string fieldpath.VersionedSet.ty mfm M mgr) $$ HM as HM
    rw [hi]
    simp only [Option.getD_some]
    ihave #Hi : isVSet i e $$ []
    · iapply Hview; ipureintro; exact ⟨hi, he⟩
    ihave ⟨%iv, %hiv⟩ := isVSet_concrete_law_holds _ _ $$ Hi
    subst hiv
    wp_auto
    wp_apply (h_versionedSet_APIVersion iv e) as %v2 %hv2
    · iexact Hi
    wp_bind (App (App (Val #(methods T go!"Convert" cvv)) (Val #p2)) (Val #v2))
    iapply HConv
    inext
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    isplitl [Hback HM]
    · iapply Hback $$ HM
      · ipureintro; exact ⟨hsorted, hdom⟩
      · iexact Hview
    rw [prune_stages_law_holds S t merged mf L hemp hmfne,
      show ensureNamed S t L.set = ensureNamedOpt S (some t) L.set from rfl]
    iexact Hp2

end proof

end smd
end EtcdGrove
end Perennial
