/-
The proof of `Model` (`Net/Spec/.../lib/remote/counter/Model.lean`): the three closures meet
`initSpec`, `stepSpec` and `equalSpec` of `cS`; the other fields are `nil`. `Init`'s `State{}` is
`State{0, 0}`, the initial set (`cSet_init`); `Step` type-asserts its arguments (a boxed `State`,
`bool` and `Out`, by `rep` and `ioOk`) and calls `step`, whose verdict and next state are the
model's (`stepG_pSeq`); `Equal`'s `==` on `State`s holds only on the same `(lo, K)`, so on the
same set (`stV_inj`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.step
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Model

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

theorem Model.wp_proof (wp_step : step.spec (GF := GF) (hG := hG)) :
    Model.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isModel isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    iintro !> %Φ' _ HΦ'
    wp_auto
    iapply HΦ'
    simp only [cS]
    ipureintro
    exact ⟨0, 0, Nat.le_refl _, by omega, rfl, cSet_init.symm⟩
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [cS]
    icases Hpre with ⟨%Hk, %Hrep, %Hio⟩
    obtain ⟨⟨b, rfl⟩, u, n, rfl⟩ := Hio
    obtain ⟨lo, K, hk, hb, rfl, rfl⟩ := Hrep
    wp_auto
    wp_apply wp_step as %ok %s' %Hst
    have H := stepG_pSeq lo K (by omega) b u n
    rw [← Hst] at H
    obtain ⟨Hok, Hs⟩ := H
    iapply HΦ'
    isplitr
    · ipureintro; exact ⟨lo, K, hk, hb, rfl, rfl⟩
    isplitr
    · ipureintro; rw [pM_box]; exact Hok
    unfold stepPost
    simp only [pM_box]
    cases hm : (EtcdGrove.linkv.pSeq cB).step (cSet lo K) (b, if u then .err else .ok n) with
    | none => simp only; itrivial
    | some S' =>
      obtain ⟨lo', K', h1, h2, h3⟩ := Hs S' hm
      simp only at h1
      subst h1 h3
      ipureintro
      exact ⟨lo', K', by omega, by omega, rfl, rfl⟩
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    iintro %k %j %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    simp only [cS]
    icases Hpre with ⟨%Hv, %Hw⟩
    obtain ⟨lo, K, hk, hb, rfl, rfl⟩ := Hv
    obtain ⟨lo', K', hj, hb', rfl, rfl⟩ := Hw
    wp_auto
    wp_if_destruct
    · iapply HΦ'
      isplitr
      · ipureintro; exact ⟨lo, K, hk, hb, rfl, rfl⟩
      isplitr
      · ipureintro; exact ⟨lo', K', hj, hb', rfl, rfl⟩
      ipureintro
      intro h
      have hK := of_decide_eq_true h
      obtain ⟨e1, e2⟩ := stV_inj hb hb' (by simp only [stV, Hif, hK])
      rw [e1, e2]
    · iapply HΦ'
      isplitr
      · ipureintro; exact ⟨lo, K, hk, hb, rfl, rfl⟩
      isplitr
      · ipureintro; exact ⟨lo', K', hj, hb', rfl, rfl⟩
      ipureintro
      nofun
  ileft
  ipureintro; trivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
