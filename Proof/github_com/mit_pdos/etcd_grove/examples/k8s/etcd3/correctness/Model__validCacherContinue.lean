module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__validCacherContinue
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__listItems
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PredOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ItemsRO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input labelSel fieldSel)


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Model.validCacherContinue.wp_proof
    (wp_listItems : Model.listItems.spec (GF := GF) (hG := hG))
    (wp_SM : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_SE : storage.SelectionPredicate.Empty.spec (GF := GF) (hG := hG))
    (wp_LM : labelSel.Matches.spec (GF := GF) (hG := hG))
    (wp_LE : labelSel.Empty.spec (GF := GF) (hG := hG))
    (wp_FM : fieldSel.Matches.spec (GF := GF) (hG := hG))
    (wp_FE : fieldSel.Empty.spec (GF := GF) (hG := hG))
    (wp_GA : getAttrs.spec (GF := GF) (hG := hG)) :
    Model.validCacherContinue.spec (GF := GF) (hG := hG) := by
  intro mp m x expC outC
  wp_start as #Hm
  ihave #Hinit := modelAt_pkg mp m $$ Hm
  ihave #Hsel := predOk_driver wp_SM wp_SE wp_LM wp_LE wp_FM wp_FE wp_GA x $$ Hinit
  unfold EtcdGrove.k8s.selPredOk
  icases Hsel with ⟨-, -, #HE⟩
  wp_auto
  ipersist opts
  ihave #opts' := opts
  iStructNamed opts'
  wp_if_destruct
  · have hP : (listOptsV x).Predicate' = predV x := rfl
    isimp only [hP] at Predicate
    wp_apply HE $$ %_ %DFrac.discard [Predicate] as -
    · iexact Predicate
    cases hpe : predEmptyL x
    · wp_auto
      wp_apply (wp_listItems mp m x x.ListKey' (listOptsV x) false rfl rfl) $$ [Hm] as %sl %err ⟨%herr, Hsl⟩
      · iexact Hm
      subst herr
      unfold objsOwn
      icases Hsl with ⟨%xs, Hsl, -, Hxs⟩
      ihave %Hlen := ownSlice_len $$ Hsl
      ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hxs
      ihave #Pr := Predicate
      iStructNamed Pr
      wp_auto
      have hv : validCacherContinueL x m [] = decide (sl.len = x.Limit') := by
        unfold validCacherContinueL
        rw [← Hlen2, Hlen.1]
        simp only [hpe, decide_true, Bool.not_false, Bool.true_and]
        apply decide_eq_decide.2
        constructor
        · intro h; word
        · intro h; rw [h] at Hlen; word
      rw [hv]
      iapply HΦ
      itrivial
    · wp_auto
      have : validCacherContinueL x m [] = false := by unfold validCacherContinueL; simp [hpe]
      rw [this]
      iapply HΦ
      itrivial
  · have : validCacherContinueL x m outC = false := by unfold validCacherContinueL; simp_all
    rw [this]
    iapply HΦ
    itrivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
