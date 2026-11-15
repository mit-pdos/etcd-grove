/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/PrepareContinueToken.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.PrepareContinueToken
public import Spec.k8s_io.apiserver.pkg.storage.EncodeContinue

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode k8s k8s_etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

theorem storage.PrepareContinueToken.wp_proof
    (wp_EncodeContinue : storage.EncodeContinue.spec (GF := GF) (hG := hG)) :
    storage.PrepareContinueToken.spec (GF := GF) (hG := hG) := by
  intro Obj S kl kp rv cnt more opts sel emp
  wp_start as #Hsel
  unfold selPredOk
  icases Hsel with ⟨%hsel, #HM, #HE⟩
  wp_auto
  cases more
  · wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ite_false]
    ipureintro
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  · wp_auto
    have h0 : (W8 0 : w8) = 0#8 := rfl
    rw [h0]
    wp_apply (wp_EncodeContinue (kl ++ [0#8]) kp rv) as %t %err %hte
    by_cases hok : encOkL (kl ++ [0#8]) kp = true
    · rw [if_pos hok] at hte
      obtain ⟨rfl, rfl⟩ := hte
      wp_auto
      iStructNamed opts
      wp_bind
      iapply HE $$ Predicate
      inext
      iintro Predicate
      cases emp
      · wp_auto
        iapply HΦ
        simp only [ite_true, hok, Bool.false_eq_true, ite_false]
        ipureintro
        repeat (first | apply And.intro | trivial | rfl)
      · wp_auto
        iapply HΦ
        simp only [ite_true, hok]
        iframe
        ipureintro
        repeat (first | apply And.intro | trivial | rfl)
    · rw [if_neg hok] at hte
      cases err with
      | nil => exact absurd rfl hte
      | ok ie =>
        wp_auto
        iapply HΦ
        simp only [ite_true, hok, Bool.false_eq_true, ite_false]
        ipureintro
        exact hte

end proof

end EtcdGrove
end Perennial
