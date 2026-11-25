/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/ParamsOk.lean`: `ParamsOk`'s `&&` chain
is one conjunct of `paramsOk` per operand, in order (the three products by `mulBelow`); a false operand
returns `false`, refuting that conjunct. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.ParamsOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI Iris.ProofMode

theorem sint_two60 : sint.Z (W64 1152921504606846976) = 2 ^ 60 := by rfl
theorem sint_two62 : sint.Z (W64 4611686018427387904) = 2 ^ 62 := by rfl

-- The pure side of a `&&` operand found false: `paramsOk` fails (the hypotheses are the operands
-- found true so far and the false one).
set_option hygiene false in
local macro "params_false" : tactic => `(tactic| (
  (try wp_auto)
  iapply HΦ
  ipureintro
  simp only [Bool.false_eq_true, false_iff, paramsOk]
  intro hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22⟩ := hp
  (try simp only [sint_two60, sint_two62] at *)
  word))

-- The next `&&` operand: split on it, the false side closed by `params_false`.
set_option hygiene false in
local macro "params_next" : tactic => `(tactic| (
  wp_if_destruct
  rotate_left
  params_false
  (try wp_auto)))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

theorem ParamsOk.wp_proof (wp_mulBelow : mulBelow.spec (GF := GF) (hG := hG)) :
    ParamsOk.spec (GF := GF) (hG := hG) := by
  intro k₁ clients ops nw nops cnw cnops k₂ k₃ k₄ k₅
  wp_start as #Hpkg
  (try wp_auto)
  -- `1 <= k1 && k1 <= 1000`
  params_next
  params_next
  -- `0 <= clients && clients < 1<<31 && 0 <= ops && mulBelow(clients, ops, 1<<60)`
  params_next
  params_next
  params_next
  wp_apply wp_mulBelow clients ops (W64 1152921504606846976) (by word) (by word)
    (by rw [sint_two60]; decide)
  params_next
  -- the watch workload, bound `1<<62`
  params_next
  params_next
  params_next
  wp_apply wp_mulBelow nw nops (W64 4611686018427387904) (by word) (by word)
    (by rw [sint_two62]; decide)
  params_next
  -- the cache workload, bound `1<<62`
  params_next
  params_next
  params_next
  wp_apply wp_mulBelow cnw cnops (W64 4611686018427387904) (by word) (by word)
    (by rw [sint_two62]; decide)
  params_next
  -- `1 <= k2 && k2 <= 300 && … && 3 <= k5 && k5 <= 300`; the last operand is the result
  params_next
  params_next
  params_next
  params_next
  params_next
  params_next
  params_next
  iapply HΦ
  ipureintro
  rw [decide_eq_true_iff]
  unfold paramsOk
  (try simp only [sint_two60, sint_two62] at *)
  constructor
  · intro h
    and_intros <;> word
  · intro hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22⟩ := hp
    word

end proof

end etcd_all
end EtcdGrove
end Perennial
