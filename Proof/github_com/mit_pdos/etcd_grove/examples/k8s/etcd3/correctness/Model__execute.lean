/-
Lean-first (no Rocq counterpart).

The proof of `(*Model).execute`: the switch on the request's operation (`reqRep`); a write clones the
receiver and runs `create`, `delete` (with `context.Background()`) or `update` on the clone, a read
runs `get` or `list` on the receiver.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__execute
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__create
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__delete
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__update
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__get
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__list
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Model.execute.wp_proof
    (wp_Clone : Model.Clone.spec (GF := GF) (hG := hG))
    (wp_create : Model.create.spec (GF := GF) (hG := hG))
    (wp_delete : Model.delete.spec (GF := GF) (hG := hG))
    (wp_update : Model.update.spec (GF := GF) (hG := hG))
    (wp_get : Model.get.spec (GF := GF) (hG := hG))
    (wp_list : Model.list.spec (GF := GF) (hG := hG)) :
    Model.execute.spec (GF := GF) (hG := hG) := by
  intro mp m x r hfit hfx hlist hsz
  wp_start as ⟨#Hm, #Hr⟩
  iunfold reqRep at Hr
  by_cases h4 : x.Kind' = W64 4
  · isimp only [h4, ↓reduceIte] at Hr
    icases Hr with %hr
    obtain ⟨hop, hkey, hopt⟩ := hr
    obtain ⟨hp, hl, hl0⟩ := hlist h4
    wp_auto
    rw [hop]
    wp_auto
    rw [hkey, hopt]
    wp_apply (wp_list mp m x hp hl hl0) as %resp #Hresp
    · iexact Hm
    have hx : rexecL x m = (rlistL x m, m, none) := by unfold rexecL; simp [h4]
    have hw : k8s_etcd3.isWriteL x = false := by unfold k8s_etcd3.isWriteL; simp [h4]
    iapply HΦ
    rw [hx, hw]
    unfold changeRep
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
    iclear «$res0» «$res1» «$res2»
    iframe
    ipureintro; trivial
  by_cases h0 : x.Kind' = W64 0
  · isimp only [h4, ↓reduceIte] at Hr
    isimp only [h0, ↓reduceIte] at Hr
    icases Hr with ⟨%hr, %op, %hob, #Hop⟩
    obtain ⟨hop, hkey⟩ := hr
    wp_auto
    rw [hop]
    wp_auto
    wp_apply (wp_Clone mp m) as %np Hnp
    · iexact Hm
    rw [hkey, hob]
    wp_apply (wp_create np m x op hsz) $$ [Hnp] as %resp %cp ⟨Hnp, #Hresp, #Hcp⟩
    · iframe Hnp Hop
    have hx : rexecL x m = rcreateL x m := by unfold rexecL; simp [h0]
    have hw : k8s_etcd3.isWriteL x = true := by unfold k8s_etcd3.isWriteL; simp [h0]
    iapply HΦ
    rw [hx, hw]
    simp only [↓reduceIte]
    iframe Hresp Hcp Hnp
  by_cases h1 : x.Kind' = W64 1
  · isimp only [h4, h0, ↓reduceIte] at Hr
    isimp only [h1, ↓reduceIte] at Hr
    icases Hr with ⟨%hr, #Hpre, #Hvf⟩
    obtain ⟨hop, hkey, hvf⟩ := hr
    wp_auto
    rw [hop]
    wp_auto
    wp_apply (wp_Clone mp m) as %np Hnp
    · iexact Hm
    wp_apply context.wp_Background
    rw [hkey]
    wp_apply (wp_delete np m x _ _ _ hfit hvf) $$ [Hnp] as %resp %cp ⟨Hnp, #Hresp, #Hcp⟩
    · iframe Hnp Hpre Hvf
    have hx : rexecL x m = rdeleteL x m := by unfold rexecL; simp [h1]
    have hw : k8s_etcd3.isWriteL x = true := by unfold k8s_etcd3.isWriteL; simp [h1]
    iapply HΦ
    rw [hx, hw]
    simp only [↓reduceIte]
    iframe Hresp Hcp Hnp
  by_cases h2 : x.Kind' = W64 2
  · isimp only [h4, h0, h1, ↓reduceIte] at Hr
    isimp only [h2, ↓reduceIte] at Hr
    icases Hr with ⟨%hr, #Hpre, #Huf⟩
    obtain ⟨hop, hkey, hig, huf⟩ := hr
    wp_auto
    rw [hop]
    wp_auto
    wp_apply (wp_Clone mp m) as %np Hnp
    · iexact Hm
    wp_apply context.wp_Background
    rw [hkey, hig]
    wp_apply (wp_update np m x _ _ _ _ hfit hfx huf hsz) $$ [Hnp] as %resp %cp ⟨Hnp, #Hresp, #Hcp⟩
    · iframe Hnp Hpre Huf
    have hx : rexecL x m = rupdateL x m := by unfold rexecL; simp [h2]
    have hw : k8s_etcd3.isWriteL x = true := by unfold k8s_etcd3.isWriteL; simp [h2]
    iapply HΦ
    rw [hx, hw]
    simp only [↓reduceIte]
    iframe Hresp Hcp Hnp
  · isimp only [h4, h0, h1, h2, ↓reduceIte] at Hr
    icases Hr with %hr
    obtain ⟨hop, hkey, hrv, hig⟩ := hr
    wp_auto
    rw [hop]
    wp_auto
    rw [hkey]
    wp_apply (wp_get mp m x _ hrv hig) as %resp #Hresp
    · iexact Hm
    have hx : rexecL x m = (rgetL x m, m, none) := by
      unfold rexecL; simp only [h4, h0, h1, h2, ↓reduceIte]
    have hw : k8s_etcd3.isWriteL x = false := by
      simp only [k8s_etcd3.isWriteL, decide_eq_false h0, decide_eq_false h1, decide_eq_false h2,
        Bool.or_false]
    iapply HΦ
    rw [hx, hw]
    unfold changeRep
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hresp
    iclear «$res0» «$res1» «$res2»
    iframe
    ipureintro; trivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
