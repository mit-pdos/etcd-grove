/-
`typed.reconcileWithSchemaWalker.reconcile`: a member of the recursion cluster `typed.reconcileWithSchemaWalkerRec` (`reconcileWithSchemaWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `reconcileWithSchemaWalker__reconcileBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcileBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doScalar
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB
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

theorem typed.reconcileWithSchemaWalker.reconcile.wp_proofBody
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (h_handleAtom : typed.handleAtom.spec (GF := GF))
    (h_reconcileWithSchemaWalker_doScalar : typed.reconcileWithSchemaWalker.doScalar.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.reconcile.specBody (GF := GF) := by
  unfold typed.reconcileWithSchemaWalker.reconcile.specBody typed.reconcileWithSchemaWalkerRec.specI
    typed.reconcileWithSchemaWalker.reconcile.specI typed.reconcileWithSchemaWalker.doList.specI
    typed.reconcileWithSchemaWalker.doMap.specI typed.reconcileWithSchemaWalker.visitListItems.specI
    typed.reconcileWithSchemaWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %F %R %A
  wp_start as ⟨Hown, %Hfind, %Hat⟩
  obtain ⟨At, hA⟩ := Option.isSome_iff_exists.1 Hfind
  iunfold rwOwn at Hown
  icases Hown with ⟨%ps, %fs, %tv, %rem, %add, %sp, Hcore, Hp, Hfs, Hrem, Hadd, Hsp⟩
  iunfold rwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  have Hnd := Schema.WF_types_nodup_law_holds S Hwf
  ihave #Htr' := (isTypeRefOpt_some_law_holds tr st.t).2 $$ Htr
  wp_auto
  wp_apply h_Schema_Resolve sc S tr (some st.t) $$ [] as %a %ok ⟨%Hok, #Ha⟩
  · iframe #; ipureintro; exact Hnd
  simp only [Schema.resolveRef, Schema.resolvesRef, Schema.resolves, hA, Option.isSome_some] at Hok ⊢
  subst Hok
  wp_auto
  ihave Hown : rwOwn w sc S st F R A $$ [Hw Hp Hfs Hrem Hadd Hsp]
  · unfold rwOwn rwCore
    iexists ps, fs, tv, rem, add, sp
    iframe Hp Hfs Hrem Hadd Hsp
    iexists tr
    iframe Hw
    iframe #
    ipureintro; exact Hwf
  icases IH with ⟨#HdL, #HdM, -, -, -⟩
  wp_apply h_handleAtom a At tr (go.GoType.PointerType typed.reconcileWithSchemaWalker.ty) #w
    iprop(rwOwn w sc S st F R A)
    (fun errs => iprop(noErrs errs ∗ ∃ R' A' : Option PathSet, rwOwn w sc S st F R' A' ∗
      ⌜optU R R' = optU R (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty)) ∧
        optU A A' = optU A (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty))⌝))
    $$ [Hown] as %errs HQ
  · iframe #
    iframe Hown
    cases At with
    | scalar sk =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_scalar_law_holds a sk).1 $$ Ha with ⟨#Hs, -⟩
      imodintro
      iintro %Φ2 Hown HΦ2
      wp_apply h_reconcileWithSchemaWalker_doScalar w sc S st F R A a.Scalar' $$ [Hown]
        as %errs ⟨Herrs, Hown⟩
      · iframe #; iframe
      iapply HΦ2
      iframe Herrs
      iexists R, A
      iframe Hown
      ipureintro
      rw [reconOut_scalar_law_holds S st.t st.path st.isAtomic _ sk hA]
      have h1 : ∀ x : Option PathSet, optU x x = optU x none := fun x => by
        have h := optU_idem_law_holds x none
        have h2 : optU x none = x := by cases x <;> rfl
        rw [h2] at h; rw [h, h2]
      exact ⟨h1 R, h1 A⟩
    | list e rel ks =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_list_law_holds a e rel ks).1 $$ Ha with ⟨-, #Hl⟩
      imodintro
      iintro %Φ2 Hown HΦ2
      wp_apply HdL $$ [Hown] as %errs HQ
      · iframe #; iframe; ipureintro; exact ⟨hA, Hat⟩
      iapply HΦ2 $$ HQ
    | map fs' e rel =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_map_law_holds a fs' e rel).1 $$ Ha with ⟨-, #Hm⟩
      imodintro
      iintro %Φ2 Hown HΦ2
      wp_apply HdM $$ [Hown] as %errs HQ
      · iframe #; iframe; ipureintro; exact ⟨hA, Hat⟩
      iapply HΦ2 $$ HQ
  iapply HΦ $$ HQ

end proof

end smd
end EtcdGrove
end Perennial
