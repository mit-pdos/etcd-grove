/-
`typed.reconcileWithSchemaWalker.finishDescent`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__finishDescent
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union

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

theorem isSetO_null (r : Loc) (o : Option PathSet) :
    isSetO (GF := GF) r o ⊢ ⌜r = null ↔ o = none⌝ := by
  rcases o with _ | s
  · unfold isSetO; iintro %h; ipureintro; simp [h]
  · unfold isSetO; iintro H
    ihave %h := isSet_not_null _ _ $$ H
    ipureintro; simp [h]

theorem typed.reconcileWithSchemaWalker.finishDescent.wp_proof
    (h_Set_Union : fieldpath.Set.Union.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.finishDescent.spec (GF := GF) :=
    fun w w2 sc S st st2 ps ps2 fs tv rem add fs2 tv2 rem2 add2 sp R A R2 A2 => by
  wp_start as ⟨Hcore, Hcore2, #HR, #HA, #HR2, #HA2, Hsp, %Hspnn, %Hcap⟩
  unfold rwCore
  icases Hcore with ⟨%tr0, Hw, #Htr, #Hsc, %HWF⟩
  icases Hcore2 with ⟨%tr2, Hw2, -⟩
  unfold spareWalkers
  icases Hsp with (%Hn | ⟨%sl, %ws, Hspp, Hws, Hwsc, Hwl⟩)
  · exact absurd Hn Hspnn
  wp_auto
  wp_join iprop(∃ p2 : fieldpath.Path, w2 ↦ (typed.reconcileWithSchemaWalker.mk null null null
      (zero_val schema.TypeRef) p2 st2.isAtomic rem2 add2 sp) ∗ v2_ptr ↦ w2) with [Hw2 v2]
      as ⟨%p2, Hw2, v2⟩
  · rw [ite_eq_left (show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
      sint.Z (W64 0) ≤ sint.Z ps2.cap) from ⟨by word, by word, by word⟩)]
    wp_auto
    wp_join_done
  ihave %HRn := isSetO_null _ _ $$ HR
  ihave %HAn := isSetO_null _ _ $$ HA
  ihave %HR2n := isSetO_null _ _ $$ HR2
  ihave %HA2n := isSetO_null _ _ $$ HA2
  wp_join iprop(∃ rem' : Loc,
      w ↦ (typed.reconcileWithSchemaWalker.mk tv sc fs tr0 ps st.isAtomic rem' add sp) ∗
      isSetO rem' (optU R R2) ∗ v_ptr ↦ w ∗ v2_ptr ↦ w2 ∗
      w2 ↦ (typed.reconcileWithSchemaWalker.mk null null null (zero_val schema.TypeRef) p2
        st2.isAtomic rem2 add2 sp))
    with [Hw v v2 Hw2] as ⟨%rem', Hw, #HR', v, v2, Hw2⟩
  · have hR2 : R2 = none := HR2n.1 rfl
    subst hR2
    iexists rem
    iframe
    rw [LawB.optU_none_r]
    iexact HR
  · obtain ⟨s2, rfl⟩ : ∃ s2, R2 = some s2 := by
      rcases R2 with _ | s2
      · exact absurd (HR2n.2 rfl) Hif
      · exact ⟨s2, rfl⟩
    wp_if_destruct
    · have hR : R = none := HRn.1 rfl
      subst hR
      wp_join_done
      iexists rem2
      iframe
      simp only [optU]
      iexact HR2
    · obtain ⟨s1, rfl⟩ : ∃ s1, R = some s1 := by
        rcases R with _ | s1
        · exact absurd (HRn.2 rfl) (by assumption)
        · exact ⟨s1, rfl⟩
      wp_apply h_Set_Union rem rem2 s1 s2 $$ [] as %r #Hr
      · iframe #
        iunfold isSetO at HR HR2
        isplitl
        · iexact HR
        · iexact HR2
      wp_join_done
      iexists r
      iframe
      simp only [optU, isSetO]
      iexact Hr
  wp_join iprop(∃ add' : Loc,
      w ↦ (typed.reconcileWithSchemaWalker.mk tv sc fs tr0 ps st.isAtomic rem' add' sp) ∗
      isSetO add' (optU A A2) ∗ v_ptr ↦ w ∗ v2_ptr ↦ w2 ∗
      w2 ↦ (typed.reconcileWithSchemaWalker.mk null null null (zero_val schema.TypeRef) p2
        st2.isAtomic rem2 add2 sp))
    with [Hw v v2 Hw2] as ⟨%add', Hw, #HA', v, v2, Hw2⟩
  · have hA2 : A2 = none := HA2n.1 rfl
    subst hA2
    iexists add
    iframe
    rw [LawB.optU_none_r]
    iexact HA
  · obtain ⟨t2, rfl⟩ : ∃ t2, A2 = some t2 := by
      rcases A2 with _ | t2
      · exact absurd (HA2n.2 rfl) Hif
      · exact ⟨t2, rfl⟩
    wp_if_destruct
    · have hA : A = none := HAn.1 rfl
      subst hA
      wp_join_done
      iexists add2
      iframe
      simp only [optU]
      iexact HA2
    · obtain ⟨t1, rfl⟩ : ∃ t1, A = some t1 := by
        rcases A with _ | t1
        · exact absurd (HAn.2 rfl) (by assumption)
        · exact ⟨t1, rfl⟩
      wp_apply h_Set_Union add add2 t1 t2 $$ [] as %r #Hr
      · iframe #
        iunfold isSetO at HA HA2
        isplitl
        · iexact HA
        · iexact HA2
      wp_join_done
      iexists r
      iframe
      simp only [optU, isSetO]
      iexact Hr
  wp_apply (wp_slice_literal (V := Loc) [w2])
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append (V := Loc) sl ws _ [w2] (DFrac.own 1))
    $$ [$Hws $Hwsc $Hsl2] as %sl' ⟨Hws, Hwsc, -⟩
  iapply HΦ
  iexists rem', add'
  iframe
  isplitr [Hw2 Hwl Hws Hwsc Hspp]
  · iframe #
    ipureintro; exact HWF
  isplitr; · iexact HR'
  isplitr; · iexact HA'
  iright
  iexists sl', ws ++ [w2]
  iframe
  iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
  ipureintro; trivial

end proof

end smd
end EtcdGrove
end Perennial
