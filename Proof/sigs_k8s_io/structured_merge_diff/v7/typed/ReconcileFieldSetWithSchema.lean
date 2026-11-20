/-
`typed.ReconcileFieldSetWithSchema`: proved (Prove phase, 2026-11-20): a pooled reconcile walker at
the root, `reconcile` (both accumulators `reconOut S t [] false s`), then nil, or
`RecursiveDifference` and `Union` (`reconOut_reconcile`; `RecursiveDifference` is `reconcile`'s
filter since the root's accumulators hold no empty path: `LawB.rdiff_eq_filter`); the walker
finished (deferred).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ReconcileFieldSetWithSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__RecursiveDifference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
public import Perennial.Spec.sync.Pool__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__finished
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcile
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers

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
variable [package_sem : typed.Assumptions]

theorem typed.ReconcileFieldSetWithSchema.wp_proof
    (h_Set_RecursiveDifference : fieldpath.Set.RecursiveDifference.spec (GF := GF))
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF))
    (h_sync_Pool_Get : _root_.Perennial.sync.Pool.Get.spec (GF := GF))
    (h_reconcileWithSchemaWalker_finished : typed.reconcileWithSchemaWalker.finished.spec (GF := GF))
    (h_reconcileWithSchemaWalker_reconcile : typed.reconcileWithSchemaWalker.reconcile.spec (GF := GF)) :
    typed.ReconcileFieldSetWithSchema.spec (GF := GF) := fun fp p sc S t x s => by
  wp_start as ⟨#Hs, #Htv, %Hcard⟩
  ihave #HP := typedPkgInit_poolsAt $$ Hpkg
  unfold typedPoolsAt
  icases HP with ⟨-, -, -, -, -, -, #Pr⟩
  icases (isTV_isTVv_law_holds p sc S t x).mp $$ Htv with ⟨%tvv, #Hp, #Htvv⟩
  iunfold isTVv at Htvv
  icases Htvv with ⟨%Hsc, #Hv, #Htr, #HS, %Hc⟩
  ihave ⟨Hp2, %Hpnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hp
  iStructNamed Hp2
  wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_sync_Pool_Get (globalAddr typed.fmPool) typed.rwNewV iprop(True)
    (pooledAs typed.reconcileWithSchemaWalker.ty rwPooled) as %y ⟨Hy, -⟩
  · iframe #
  icases Hy with (Hy | %hnil)
  rotate_left
  · exfalso; obtain ⟨h, -⟩ := hnil; simp [typed.rwNewV, func.nil] at h
  iunfold pooledAs at Hy
  icases Hy with ⟨%wl, %hy, Hw0⟩
  subst hy
  iunfold rwPooled at Hw0
  icases Hw0 with ⟨%v0, Hw, %Hv0, Hsp⟩
  obtain ⟨hpath, hat, hrem, hadd⟩ := Hv0
  wp_auto
  simp only
  ihave Hown : rwOwn wl sc S (RWSt.mk t [] false) (some s) none none v0.spareWalkers' $$ [Hw Hsp]
  · unfold rwOwn rwCore
    iexists v0.path', fp, p, v0.toRemove', v0.toAdd'
    iframe
    isplitl [Hw]
    · iexists tvv.typeRef'
      rw [← hat, ← Hsc]
      iframe
      iframe #
      ipureintro; exact Hc.1
    rw [hpath]
    isplitr
    · iapply (show ⊢ ownPath (GF := GF) slice.nil [] from ownPath_nil_law_holds)
    unfold isSetO
    iframe #
    ipureintro; exact ⟨hrem, hadd⟩
  wp_apply h_reconcileWithSchemaWalker_reconcile wl sc S (RWSt.mk t [] false) (some s) none none
      v0.spareWalkers' $$ [Hown] as %errs ⟨Herrs, %R', %A', ⟨%sp', Hown, -⟩, %HRA⟩
  · iframe
    ipureintro
    refine ⟨LawA.conforms_find S t x Hc.2, fun h => by simp at h, ?_⟩
    simpa using Hcard
  ihave %Hlen := noErrs_len $$ Herrs
  have hd : ¬ (sint.Z (W64 0) < sint.Z errs.len) := by rw [Hlen]; simp
  rw [decide_eq_false hd]
  simp only [optU] at HRA
  obtain ⟨rfl, rfl⟩ := HRA
  have hlaw := reconOut_reconcile_law_holds S t s Hc.1
  iunfold rwOwn at Hown
  icases Hown with ⟨%ps', %fs', %tv', %rem', %add', Hcore, Hp', Hfs, Hrem, Hadd, Hsp'⟩
  iunfold rwCore at Hcore
  icases Hcore with ⟨%tr', Hw, #Htr', #Hsc', %Hwf'⟩
  simp only [Option.getD]
  iunfold isSetO at Hfs
  icases Hfs with #Hfs
  ihave %Hfsn := isSet_not_null fs' s $$ Hfs
  wp_auto
  revert hlaw
  cases hN : reconOut S t [] false s with
  | none =>
    intro hlaw
    iunfold isSetO at Hrem Hadd
    icases Hrem with %Hrem
    icases Hadd with %Hadd
    subst Hrem Hadd
    wp_auto
    wp_apply h_reconcileWithSchemaWalker_finished wl sc S (RWSt.mk t [] false) ps' fs' tv' null null sp'
      $$ [Hw Hsp']
    · iframe
      unfold rwCore
      isplitl [Hw]
      · iexists tr'
        iframe
        iframe #
        ipureintro; exact Hwf'
      ipureintro; rfl
    iapply HΦ
    isplitr
    · ipureintro; rfl
    ileft
    ipureintro; exact ⟨rfl, hlaw⟩
  | some N =>
    intro hlaw
    iunfold isSetO at Hrem Hadd
    icases Hrem with #Hrem
    icases Hadd with #Hadd
    ihave %Hremn := isSet_not_null rem' N $$ Hrem
    ihave %Haddn := isSet_not_null add' N $$ Hadd
    rw [decide_eq_false Haddn]
    wp_auto
    rw [decide_eq_false Hremn]
    wp_auto
    wp_apply h_Set_RecursiveDifference fs' rem' s N $$ [] as %o1 #Ho1
    · iframe #
    rw [decide_eq_false Haddn]
    wp_auto
    wp_apply h_Set_Union o1 add' (PathSet.rdiff s N) N $$ [] as %o2 #Ho2
    · iframe #
    try wp_auto
    wp_apply h_reconcileWithSchemaWalker_finished wl sc S (RWSt.mk t [] false) ps' fs' tv' rem' add' sp'
      $$ [Hw Hsp']
    · iframe
      unfold rwCore
      isplitl [Hw]
      · iexists tr'
        iframe
        iframe #
        ipureintro; exact Hwf'
      ipureintro; rfl
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iright
    simp only at hlaw
    rw [hlaw, ← LawB.rdiff_eq_filter s N (LawB.reconOut_root_ne S t s N hN)]
    rw [show FSet.union (PathSet.rdiff s N) N = PathSet.union (PathSet.rdiff s N) N from rfl]
    iexact Ho2

end proof

end smd
end EtcdGrove
end Perennial
