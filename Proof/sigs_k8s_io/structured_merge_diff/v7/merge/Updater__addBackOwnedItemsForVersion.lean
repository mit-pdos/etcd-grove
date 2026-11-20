/-
`merge.Updater.addBackOwnedItemsForVersion`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `typed.TypedValue.ToFieldSet`, `typed.TypedValue.Schema`,
`typed.TypedValue.TypeRef`, `fieldpath.Set.EnsureNamedFieldsAreMembers`, `fieldpath.Set.Union`,
`fieldpath.Set.Difference`, `typed.TypedValue.RemoveItems`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackOwnedItemsForVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Difference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
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

theorem merge.Updater.addBackOwnedItemsForVersion.wp_proof
    (h_Set_Difference : fieldpath.Set.Difference.spec (GF := GF))
    (h_Set_EnsureNamedFieldsAreMembers : fieldpath.Set.EnsureNamedFieldsAreMembers.spec (GF := GF))
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF))
    (h_TypedValue_RemoveItems_ptr : typed.TypedValue.RemoveItems_ptr.spec (GF := GF))
    (h_TypedValue_Schema_ptr : typed.TypedValue.Schema_ptr.spec (GF := GF))
    (h_TypedValue_ToFieldSet_ptr : typed.TypedValue.ToFieldSet_ptr.spec (GF := GF))
    (h_TypedValue_TypeRef_ptr : typed.TypedValue.TypeRef_ptr.spec (GF := GF)) :
    merge.Updater.addBackOwnedItemsForVersion.spec (GF := GF) :=
    fun u cv igf igfl rion sc S t mp merged pp pruned ver ms managed => by
  wp_start as ⟨#Hu, #Hcv, #Hm, #Hp, #Hman, %hpre⟩
  obtain ⟨hms, hps, hman, hconf⟩ := hpre
  unfold isUpdater isIdentityConverter
  icases Hcv with ⟨%T, %cvv, %hcv, #HConv, #HMiss⟩
  subst hcv
  iStructNamed Hu
  wp_auto
  wp_bind (App (App (Val #(methods T go!"Convert" cvv)) (Val #mp)) (Val #ver))
  iapply HConv
  inext
  wp_auto
  wp_bind (App (App (Val #(methods T go!"Convert" cvv)) (Val #pp)) (Val #ver))
  iapply HConv
  inext
  wp_auto
  wp_apply (h_TypedValue_ToFieldSet_ptr mp sc S t merged) as %mset %merr ⟨%hmerr, Hmset⟩
  · iframe Hm; ipureintro; exact hms
  subst hmerr
  wp_auto
  wp_apply (h_TypedValue_ToFieldSet_ptr pp sc S t pruned) as %pset %perr ⟨%hperr, Hpset⟩
  · iframe Hp; ipureintro; exact hps
  subst hperr
  wp_auto
  wp_apply (h_TypedValue_Schema_ptr mp sc S t merged)
  · iexact Hm
  wp_apply (h_TypedValue_TypeRef_ptr mp sc S t merged) as %tr #Htr
  · iexact Hm
  try wp_auto
  imod (ownSet_persist_law_holds _ _) $$ Hmset with #Hmset
  imod (ownSet_persist_law_holds _ _) $$ Hpset with #Hpset
  ihave ⟨#Hsc, %hwf⟩ := isTV_schema_law_holds _ _ _ _ _ $$ Hm
  ihave #Htro := (isTypeRefOpt_some_law_holds tr t).2 $$ Htr
  ihave %hne := isSet_ne_law_holds _ _ $$ Hman
  wp_apply (h_Set_EnsureNamedFieldsAreMembers ms _ sc S tr (some t)) as %ms2 #Hms2
  · iframe Hman Hsc Htro; ipureintro; exact ⟨hwf, nodes_cardLt _ hne hman⟩
  try wp_auto
  wp_apply (h_Set_EnsureNamedFieldsAreMembers pset _ sc S tr (some t)) as %ps2 #Hps2
  · iframe Hpset Hsc Htro; ipureintro; exact ⟨hwf, fieldSet_cardLt _ _ _ hps⟩
  try wp_auto
  wp_apply (h_Set_Union ps2 ms2 _ _) as %un #Hun
  · isplitr
    · iexact Hps2
    · iexact Hms2
  try wp_auto
  wp_apply (h_Set_EnsureNamedFieldsAreMembers mset _ sc S tr (some t)) as %mset2 #Hmset2
  · iframe Hmset Hsc Htro; ipureintro; exact ⟨hwf, fieldSet_cardLt _ _ _ hms⟩
  try wp_auto
  wp_apply (h_Set_Difference mset2 un _ _) as %d #Hd
  · isplitr
    · iexact Hmset2
    · iexact Hun
  try wp_auto
  wp_apply (h_TypedValue_RemoveItems_ptr mp d sc S t merged _) as %r #Hr
  · iframe Hm Hd; ipureintro
    exact hconf
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  rw [show addBackOwned S t merged pruned managed = removeItems S t merged
    ((ensureNamedOpt S (some t) (fieldSet S t merged)).diff
      ((ensureNamedOpt S (some t) (fieldSet S t pruned)).union (ensureNamedOpt S (some t) managed))) from rfl]
  iexact Hr

end proof

end smd
end EtcdGrove
end Perennial
