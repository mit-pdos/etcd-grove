/-
`merge.Updater.addBackDanglingItems`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `fieldpath.versionedSet.Set`, `fieldpath.versionedSet.APIVersion`,
`typed.TypedValue.ToFieldSet`, `typed.TypedValue.Schema`, `typed.TypedValue.TypeRef`,
`fieldpath.Set.EnsureNamedFieldsAreMembers`, `fieldpath.Set.Difference`,
`fieldpath.Set.Intersection`, `typed.TypedValue.RemoveItems`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackDanglingItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Difference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Intersection
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__RemoveItems_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Schema_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__ToFieldSet_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__TypeRef_ptr
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsStage

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

theorem merge.Updater.addBackDanglingItems.wp_proof
    (h_Set_Difference : fieldpath.Set.Difference.spec (GF := GF))
    (h_Set_EnsureNamedFieldsAreMembers : fieldpath.Set.EnsureNamedFieldsAreMembers.spec (GF := GF))
    (h_Set_Intersection : fieldpath.Set.Intersection.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF))
    (h_TypedValue_RemoveItems_ptr : typed.TypedValue.RemoveItems_ptr.spec (GF := GF))
    (h_TypedValue_Schema_ptr : typed.TypedValue.Schema_ptr.spec (GF := GF))
    (h_TypedValue_ToFieldSet_ptr : typed.TypedValue.ToFieldSet_ptr.spec (GF := GF))
    (h_TypedValue_TypeRef_ptr : typed.TypedValue.TypeRef_ptr.spec (GF := GF)) :
    merge.Updater.addBackDanglingItems.spec (GF := GF) :=
    fun u cv igf igfl rion sc S t mp merged pp pruned ls L => by
  wp_start as ⟨#Hu, #Hcv, #Hm, #Hp, #Hls, %hpre⟩
  obtain ⟨hms, hps, hls, hconf⟩ := hpre
  unfold isUpdater isIdentityConverter
  icases Hcv with ⟨%T, %cvv, %hcv, #HConv, #HMiss⟩
  ihave ⟨%lv, %hlv⟩ := isVSet_concrete_law_holds _ _ $$ Hls
  subst hlv hcv
  wp_auto
  wp_apply (h_versionedSet_APIVersion lv L) as %ver %hver
  · iexact Hls
  irename : (u ↦□ (_ : merge.Updater) : IProp GF) => Hu
  iStructNamed Hu
  wp_auto
  wp_bind (App (App (Val #(methods T go!"Convert" cvv)) (Val #pp)) (Val #ver))
  iapply HConv
  inext
  wp_auto
  wp_apply (h_TypedValue_ToFieldSet_ptr pp sc S t pruned) as %ps %perr ⟨%hperr, Hps⟩
  · iframe Hp; ipureintro; exact hps
  subst hperr
  wp_auto
  wp_apply (h_TypedValue_ToFieldSet_ptr mp sc S t merged) as %ms %merr ⟨%hmerr, Hms⟩
  · iframe Hm; ipureintro; exact hms
  subst hmerr
  wp_auto
  wp_apply (h_TypedValue_Schema_ptr mp sc S t merged)
  · iexact Hm
  wp_apply (h_TypedValue_TypeRef_ptr mp sc S t merged) as %tr #Htr
  · iexact Hm
  try wp_auto
  imod (ownSet_persist_law_holds _ _) $$ Hps with #Hps
  imod (ownSet_persist_law_holds _ _) $$ Hms with #Hms
  ihave ⟨#Hsc, %hwf⟩ := isTV_schema_law_holds _ _ _ _ _ $$ Hm
  ihave #Htro := (isTypeRefOpt_some_law_holds tr t).2 $$ Htr
  wp_apply (h_Set_EnsureNamedFieldsAreMembers ps _ sc S tr (some t)) as %ps2 #Hps2
  · iframe Hps Hsc Htro; ipureintro; exact ⟨hwf, fieldSet_cardLt _ _ _ hps⟩
  wp_apply (h_Set_EnsureNamedFieldsAreMembers ms _ sc S tr (some t)) as %ms2 #Hms2
  · iframe Hms Hsc Htro; ipureintro; exact ⟨hwf, fieldSet_cardLt _ _ _ hms⟩
  wp_auto
  wp_apply (h_versionedSet_Set lv L) as %ls1 #Hls1
  · iexact Hls
  ihave %hne := isSet_ne_law_holds _ _ $$ Hls1
  wp_apply (h_Set_EnsureNamedFieldsAreMembers ls1 _ sc S tr (some t)) as %ls2 #Hls2
  · iframe Hls1 Hsc Htro; ipureintro; exact ⟨hwf, nodes_cardLt _ hne hls⟩
  wp_auto
  wp_apply (h_Set_Difference ms2 ps2 _ _) as %d #Hd
  · isplitr
    · iexact Hms2
    · iexact Hps2
  wp_apply (h_Set_Intersection d ls2 _ _) as %i #Hi
  · isplitr
    · iexact Hd
    · iexact Hls2
  wp_auto
  wp_apply (h_TypedValue_RemoveItems_ptr mp i sc S t merged _) as %r #Hr
  · iframe Hm Hi; ipureintro
    exact hconf
  iapply HΦ
  isplitr
  · ipureintro; rfl
  rw [show addBackDangling S t merged pruned L.set = removeItems S t merged
    (((ensureNamedOpt S (some t) (fieldSet S t merged)).diff (ensureNamedOpt S (some t) (fieldSet S t pruned))).inter
      (ensureNamedOpt S (some t) L.set)) from rfl]
  iexact Hr

end proof

end smd
end EtcdGrove
end Perennial
