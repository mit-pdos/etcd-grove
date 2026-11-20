/-
`merge.Updater.Update`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Lean-first (2026-11-19).
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
  have hsz : live.size < smdSizeMax ∧ new.size < smdSizeMax := by
    obtain ⟨h1, -⟩ := hsmall
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1
    omega
  wp_auto
  wp_apply (h_Updater_reconcileManagedFieldsWithSchemaChanges u cv _ _ rion sc S t lp live mfm mf)
    as %r0 %err0 ⟨%herr0, Hr0⟩
  · iframe Hu Hcv Hl Hmf
  subst herr0
  wp_auto
  wp_apply (h_Updater_update u cv rion sc S t lp live np new ver r0 (reconcileMF S t mf) mgr true) $$ [Hr0]
    as %r1 %cp %err1 Hpost
  · iframe Hu Hcv Hl Hn Hr0; ipureintro; exact hsz
  icases Hpost with ⟨%h1, Hr0, #Hcmp⟩
  obtain ⟨rfl, rfl⟩ := h1
  wp_auto
  trace_state
  sorry

end proof

end smd
end EtcdGrove
end Perennial
