/-
`typed.compareWalker.doLeaf`: proved (Prove phase, 2026-11-19): in a leaf already, nothing; else
mark the walker in a leaf and insert its path into the comparison's added, removed or modified set
(`leafC`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doLeaf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsing
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB

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

theorem typed.compareWalker.doLeaf.wp_proof
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_EqualsUsing : value.EqualsUsing.spec (GF := GF)) :
    typed.compareWalker.doLeaf.spec (GF := GF) := fun w sc S st c C dql dqr l r sp => by
  wp_start as ⟨Hown, Hl, Hr, %Hpre⟩
  iNamed Hown
  icases Hown with ⟨Hcore, Hps, Hsp, Ha, Hc⟩
  iNamed Hcore
  icases Hcore with ⟨Hw, #Htr, #Hsc, %HWF⟩
  wp_auto
  cases Hif : st.inLeaf
  rotate_left
  · wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    unfold cwOwn cwCore; rw [Hif]
    iexists ps, a
    iframe
    isplitr; iexact Htr
    isplitr; iexact Hsc
    ipureintro; exact HWF
  · wp_auto
    unfold ownCmp
    icases Hc with ⟨%rm, %md, %ad, Hcs, Hrm, Hmd, Had⟩
    unfold ownPath
    icases Hps with ⟨Hpf, Hcap⟩
    rcases l with _ | x
    · ihave ⟨Hl, %Hln⟩ := isValO_nil $$ Hl
      rw [Hln.2 rfl]
      wp_auto
      have hcard : C.added.CardLt (2 ^ 63 - 1) := by
        have := Hpre.2.2.2
        simp only [Cmp.union, leafC] at this
        exact LawB.cardLt_union_left _ _ _ this
      wp_apply h_Set_Insert ad C.added ps (DFrac.own 1) st.path $$ [Had Hpf] as ⟨Had, Hpf⟩
      · iframe; ipureintro; exact hcard
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte, leafC, Cmp.union, LawB.ps_union_empty]
      iframe
      unfold cwOwn cwCore ownPath ownCmp
      iexists ps, a
      iframe
      simp only
      isplitr; iexact Htr
      isplitr; iexact Hsc
      ipureintro; exact HWF
    · ihave ⟨Hl, %Hlp⟩ := isValO_some $$ Hl
      obtain ⟨pl, Hpl⟩ := Hlp
      rw [Hpl]
      wp_auto
      rcases r with _ | y
      · ihave ⟨Hr, %Hrn⟩ := isValO_nil $$ Hr
        rw [Hrn.2 rfl]
        wp_auto
        have hcard : C.removed.CardLt (2 ^ 63 - 1) := by
          have := Hpre.2.1
          simp only [Cmp.union, leafC] at this
          exact LawB.cardLt_union_left _ _ _ this
        wp_apply h_Set_Insert rm C.removed ps (DFrac.own 1) st.path $$ [Hrm Hpf] as ⟨Hrm, Hpf⟩
        · iframe; ipureintro; exact hcard
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte, leafC, Cmp.union, LawB.ps_union_empty]
        iframe
        unfold cwOwn cwCore ownPath ownCmp
        iexists ps, a
        iframe
        simp only
        isplitr; iexact Htr
        isplitr; iexact Hsc
        ipureintro; exact HWF
      · ihave ⟨Hr, %Hrp⟩ := isValO_some $$ Hr
        obtain ⟨pr, Hpr⟩ := Hrp
        rw [Hpr]
        simp only [isValO]
        wp_auto
        wp_apply h_EqualsUsing a _ _ dqr dql y x $$ [Ha Hr Hl] as %b ⟨Ha, Hr, Hl, %Hb⟩
        · iframe
        by_cases hxy : x = y
        · have hb : b = true := Hb.2 hxy.symm
          subst hb hxy
          wp_auto
          iapply HΦ
          simp only [Bool.false_eq_true, ↓reduceIte, leafC, Cmp.union, Cmp.none,
            LawB.ps_union_empty]
          iframe
          unfold cwOwn cwCore ownPath ownCmp
          iexists ps, a
          iframe
          simp only
          isplitr; iexact Htr
          isplitr; iexact Hsc
          ipureintro; exact HWF
        · have hb : b = false := by
            cases b
            · rfl
            · exact absurd (Hb.1 rfl).symm hxy
          subst hb
          wp_auto
          have hcard : C.modified.CardLt (2 ^ 63 - 1) := by
            have := Hpre.2.2.1
            simp only [Cmp.union, leafC, hxy, ↓reduceIte] at this
            exact LawB.cardLt_union_left _ _ _ this
          wp_apply h_Set_Insert md C.modified ps (DFrac.own 1) st.path $$ [Hmd Hpf] as ⟨Hmd, Hpf⟩
          · iframe; ipureintro; exact hcard
          iapply HΦ
          simp only [Bool.false_eq_true, ↓reduceIte, leafC, hxy, Cmp.union, LawB.ps_union_empty]
          iframe
          unfold cwOwn cwCore ownPath ownCmp
          iexists ps, a
          iframe
          simp only
          isplitr; iexact Htr
          isplitr; iexact Hsc
          ipureintro; exact HWF

end proof

end smd
end EtcdGrove
end Perennial
