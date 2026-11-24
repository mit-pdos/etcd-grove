/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/ParamsOk.lean`: `ParamsOk`'s `&&` chain
is `paramsOk`'s range conjuncts, one per operand, then the two products by `mulBelow`: `clients·ops`
below `2^60`, then `watchers·wops` below what is left, `2^60 - clients·ops` (computed without overflow
once the first holds); a false operand returns `false`, refuting `paramsOk`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.ParamsOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI Iris.ProofMode

theorem sint_two60 : sint.Z (W64 1152921504606846976) = 2 ^ 60 := by rfl

/-- `2^60 - clients·ops` on `int`s, once the product is below `2^60`. -/
theorem sint_rest (c o : w64) (h0 : 0 ≤ sint.Z c * sint.Z o) (h1 : sint.Z c * sint.Z o < 2 ^ 60) :
    sint.Z (W64 1152921504606846976 - c * o) = 2 ^ 60 - sint.Z c * sint.Z o := by
  have hm : sint.Z (c * o) = sint.Z c * sint.Z o := by
    change (c * o).toInt = c.toInt * o.toInt
    change 0 ≤ c.toInt * o.toInt at h0
    change c.toInt * o.toInt < 2 ^ 60 at h1
    rw [BitVec.toInt_mul]
    apply Int.bmod_eq_of_le <;> omega
  generalize c * o = u at hm ⊢
  word

-- The pure side of an operand found false: `paramsOk` fails.
set_option hygiene false in
local macro "params_false" : tactic => `(tactic| (
  (try wp_auto)
  iapply HΦ
  ipureintro
  simp only [Bool.false_eq_true, false_iff, paramsOk]
  intro hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  have := Int.mul_nonneg h5 h8
  have := Int.mul_nonneg h6 h9
  (try simp only [sint_two60] at *)
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

theorem ParamsOk.wp_proof (wp_mulBelow : mulBelow.spec (GF := GF) (hG := hG)) :
    ParamsOk.spec (GF := GF) (hG := hG) := by
  intro k₁ clients ops watchers wops k₂
  wp_start as #Hpkg
  (try wp_auto)
  -- `1 <= k1 && k1 <= 1000 && 1 <= k2 && k2 <= 600`
  params_next
  params_next
  params_next
  params_next
  -- `0 <= clients && 0 <= watchers && clients < 1<<31 && watchers < 1<<31-clients`
  params_next
  params_next
  params_next
  params_next
  -- `0 <= ops && 0 <= wops`
  params_next
  params_next
  -- the range facts, by name
  have rc : 0 ≤ sint.Z clients := by word
  have rw' : 0 ≤ sint.Z watchers := by word
  have ro : 0 ≤ sint.Z ops := by word
  have rwo : 0 ≤ sint.Z wops := by word
  have hco0 : 0 ≤ sint.Z clients * sint.Z ops := Int.mul_nonneg rc ro
  have hwo0 : 0 ≤ sint.Z watchers * sint.Z wops := Int.mul_nonneg rw' rwo
  -- `mulBelow(clients, ops, 1<<60)`
  wp_apply wp_mulBelow clients ops (W64 1152921504606846976) rc ro
    (by rw [sint_two60]; decide)
  params_next
  -- `mulBelow(watchers, wops, 1<<60 - clients*ops)`
  have hco : sint.Z clients * sint.Z ops < 2 ^ 60 := by
    have h := Hif
    (try simp only [sint_two60] at h)
    omega
  have hrest := sint_rest clients ops hco0 hco
  wp_apply wp_mulBelow watchers wops (W64 1152921504606846976 - clients * ops) rw' rwo
    (by rw [hrest]; exact Int.sub_pos.2 hco)
  iapply HΦ
  ipureintro
  rw [decide_eq_true_iff, hrest]
  unfold paramsOk
  constructor
  · intro h
    have htot : sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60 := by
      exact Int.add_lt_of_lt_sub_left h
    refine ⟨?_, ?_, ?_, ?_, rc, rw', ?_, ro, rwo, htot⟩ <;> word
  · intro hp
    have htot := hp.2.2.2.2.2.2.2.2.2
    exact Int.lt_sub_left_of_add_lt htot

end proof

end k8s_all
end EtcdGrove
end Perennial
