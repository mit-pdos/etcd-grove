/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/ParamsOk.lean`: `ParamsOk`'s `&&` is
one conjunct of `paramsOk` per operand; a false first operand returns `false`, refuting that conjunct.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.ParamsOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

theorem ParamsOk.wp_proof :
    ParamsOk.spec (GF := GF) (hG := hG) := by
  intro k₅
  wp_start as #Hpkg
  (try wp_auto)
  -- `3 <= k5 && k5 <= 300`; the last operand is the result
  wp_if_destruct
  rotate_left
  · (try wp_auto)
    iapply HΦ
    ipureintro
    simp only [Bool.false_eq_true, false_iff, paramsOk]
    intro hp
    obtain ⟨h1, h2⟩ := hp
    word
  (try wp_auto)
  iapply HΦ
  ipureintro
  rw [decide_eq_true_iff]
  unfold paramsOk
  constructor
  · intro h
    and_intros <;> word
  · intro hp
    obtain ⟨h1, h2⟩ := hp
    word

end proof

end etcd_all
end EtcdGrove
end Perennial
