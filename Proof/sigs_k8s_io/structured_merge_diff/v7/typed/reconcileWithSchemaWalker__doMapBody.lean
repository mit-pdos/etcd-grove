/-
`typed.reconcileWithSchemaWalker.doMap`: a member of the recursion cluster `typed.reconcileWithSchemaWalkerRec` (`reconcileWithSchemaWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `reconcileWithSchemaWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Size
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.isUntypedDeducedMap
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

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

theorem typed.reconcileWithSchemaWalker.doMap.wp_proofBody
    (h_NewSet : fieldpath.NewSet.spec (GF := GF))
    (h_Set_Size : fieldpath.Set.Size.spec (GF := GF))
    (h_isUntypedDeducedMap : typed.isUntypedDeducedMap.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.doMap.specBody (GF := GF) := by
  unfold typed.reconcileWithSchemaWalker.doMap.specBody typed.reconcileWithSchemaWalkerRec.specI
    typed.reconcileWithSchemaWalker.reconcile.specI typed.reconcileWithSchemaWalker.doList.specI
    typed.reconcileWithSchemaWalker.doMap.specI typed.reconcileWithSchemaWalker.visitListItems.specI
    typed.reconcileWithSchemaWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %F %R %A %tp %fs' %e %rel
  wp_start as ⟨Hown, #Hm, %Hfind, %Hat⟩
  iunfold rwOwn at Hown
  icases Hown with ⟨%ps, %fs, %tv, %rem, %add, %sp, Hcore, Hp, Hfs, Hrem, Hadd, Hsp⟩
  iunfold rwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  icases isMapRep_elim_law_holds tp fs' e rel $$ Hm with
    ⟨%fsl, %sfs, %etv, -, -, -, -, -, -, -, #Hrel⟩
  wp_auto
  wp_apply h_isUntypedDeducedMap tp fs' e rel $$ [] as %b %Hb
  · iframe #
  have hb : b = false := by
    cases b
    · rfl
    · exact absurd (Hb rfl) (LawB.map_elem_not_untyped S Hwf _ _ _ _ Hfind)
  subst hb
  wp_pures
  rcases hb : st.isAtomic
  · wp_auto
    by_cases hr : rel = .atomic
    · subst hr
      have hg : decide (ElemRel.goName .atomic = go!"atomic") = true := by decide
      rw [hg]
      wp_auto
      rcases F with _ | F'
      · have ht : reconTouch S st.t false PathSet.empty = false := by
          simp [reconTouch, Hfind, PathSet.empty]
          rfl
        iunfold isSetO at Hfs
        icases Hfs with %Hfs
        subst Hfs
        wp_auto
        iapply HΦ
        isplitr
        · iapply noErrs_nil
        iexists R, A
        isplitl
        · unfold rwOwn rwCore
          iexists ps, null, tv, rem, add, sp
          iframe
          isplitl [Hw]
          · iexists tr
            rw [hb]
            iframe
            iframe #
            ipureintro
            exact Hwf
          iunfold isSetO
          ipureintro; rfl
        ipureintro
        simp only [Option.getD]
        rw [LawB.reconOut_empty _ _ _ _ (ht), LawB.optU_self, LawB.optU_self]
        exact ⟨rfl, rfl⟩
      -- a non-empty child set of a granular-to-atomic map: `NewSet(v.path)` takes the walker's
      -- path as a persistent `isPaths` (the walker owns it, `ownPath`), and `Set.Size`'s result is
      -- unconstrained without a bound on the set's count
      · sorry
    have hg : decide (rel.goName = go!"atomic") = false := by
      cases rel <;> first | exact absurd rfl hr | decide
    rw [hg]
    wp_auto
    have ht : ∀ F', reconTouch S st.t false F' = false := fun F' => by
      cases rel <;> simp_all [reconTouch]
    rcases F with _ | F'
    · iunfold isSetO at Hfs
      icases Hfs with %Hfs
      subst Hfs
      wp_auto
      iapply HΦ
      isplitr
      · iapply noErrs_nil
      iexists R, A
      isplitl
      · unfold rwOwn rwCore
        iexists ps, null, tv, rem, add, sp
        iframe
        isplitl [Hw]
        · iexists tr
          rw [hb]
          iframe
          iframe #
          ipureintro
          exact Hwf
        iunfold isSetO
        ipureintro; rfl
      ipureintro
      simp only [Option.getD]
      rw [LawB.reconOut_empty _ _ _ _ (ht _), LawB.optU_self, LawB.optU_self]
      exact ⟨rfl, rfl⟩
    · iunfold isSetO at Hfs
      ihave #Hfs := Hfs
      ihave %Hfsn := isSet_not_null fs F' $$ Hfs
      rw [decide_eq_false Hfsn]
      wp_auto
      icases IH with ⟨-, -, -, -, #HvM⟩
      wp_apply HvM $$ [Hw Hp Hrem Hadd Hsp] as %errs ⟨Herrs, %R', %A', Hown, %HRA⟩
      · iframe #
        isplitl
        · unfold rwOwn rwCore
          iexists ps, fs, tv, rem, add, sp
          iframe
          isplitl [Hw]
          · iexists tr
            rw [hb]
            iframe
            iframe #
            ipureintro
            exact Hwf
          iunfold isSetO
          iexact Hfs
        ipureintro
        exact ⟨Hfind, hr⟩
      wp_auto
      iapply HΦ
      iframe Herrs
      iexists R', A'
      iframe Hown
      ipureintro
      simp only [Option.getD]
      rw [reconOut_granular_law_holds _ _ _ _ _ (ht _)]
      exact HRA
  · have hF := Hat hb
    subst hF
    wp_auto
    have ht : reconTouch S st.t true PathSet.empty = false := by simp [reconTouch]
    iunfold isSetO at Hfs
    icases Hfs with %Hfs
    subst Hfs
    wp_auto
    iapply HΦ
    isplitr
    · iapply noErrs_nil
    iexists R, A
    isplitl
    · unfold rwOwn rwCore
      iexists ps, null, tv, rem, add, sp
      iframe
      isplitl [Hw]
      · iexists tr
        rw [hb]
        iframe
        iframe #
        ipureintro
        exact Hwf
      iunfold isSetO
      ipureintro; rfl
    ipureintro
    simp only [Option.getD]
    rw [LawB.reconOut_empty _ _ _ _ (ht), LawB.optU_self, LawB.optU_self]
    exact ⟨rfl, rfl⟩

end proof

end smd
end EtcdGrove
end Perennial
