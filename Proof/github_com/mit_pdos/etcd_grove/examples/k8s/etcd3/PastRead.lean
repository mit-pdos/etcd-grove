/- Lean-first (no Rocq counterpart). `PastRead`'s proof (k8s-dist K9 step 5). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PastRead
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pastRead

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem PastRead.wp_proof
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_pastRead : pastRead.spec (GF := GF) (hG := hG)) :
    PastRead.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as -
  wp_auto
  wp_apply wp_parseRV as %n %err Hp
  cases hp : parseRVD x.MinRV' with
  | none =>
    isimp only [hp] at Hp
    icases Hp with ⟨%hne, -⟩
    cases err with
    | nil => exact absurd rfl hne
    | ok i =>
      (try wp_auto)
      rw [show pastReadPubL x = false by simp [pastReadPubL, hp]]
      iapply HΦ; itrivial
  | some q =>
    isimp only [hp] at Hp
    icases Hp with ⟨%he, %hm⟩
    subst he hm
    (try wp_auto)
    wp_if_destruct
    · wp_apply wp_pastRead
      (try wp_auto)
      rw [show pastReadPubL x = pastReadL x n by simp [pastReadPubL, hp, Hif]]
      iapply HΦ; itrivial
    · have h4 : ¬ x.Kind' = W64 4 := by simpa using Hif
      have hsome : pastReadPubL x = if x.Kind' = W64 4 then pastReadL x n
          else decide (x.Kind' = W64 5) && decide (n ≠ W64 0) := by simp only [pastReadPubL, hp]
      (try wp_auto)
      by_cases h5 : x.Kind' = W64 5
      · rw [decide_eq_true h5]
        (try wp_auto)
        rw [show pastReadPubL x = decide (uint.Z (W64 0) < uint.Z n) by
          rw [hsome, if_neg h4, decide_eq_true h5, Bool.true_and, decide_eq_decide]
          constructor <;> intro h <;> word]
        iapply HΦ; itrivial
      · rw [decide_eq_false h5]
        (try wp_auto)
        rw [show pastReadPubL x = false by rw [hsome, if_neg h4, decide_eq_false h5, Bool.false_and]]
        iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
