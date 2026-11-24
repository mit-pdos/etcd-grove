/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.OneWaiting`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OneWaiting
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.confsAfterCount
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `s.F[k]` of an `intsRO` slice. -/
theorem State.OneWaiting_intsRO_at (sl : GoSlice) (xs : List Int) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < xs.length) :
    intsRO (GF := GF) sl xs ⊢ ∃ w : w64, sliceAt sl k w ∗ ⌜sint.Z w = xs[sint.nat k]!⌝ := by
  iintro #H
  iunfold intsRO at H
  icases H with ⟨%ws, #Hws, %Hmap⟩
  subst Hmap
  iapply sliceRel_at (fun (w : w64) (x : Int) => sint.Z w = x) sl ws (ws.map sint.Z) k hk
    (by
      clear hk
      induction ws with
      | nil => exact .nil
      | cons w ws ih => exact .cons rfl ih)
  iexact Hws

theorem State.OneWaiting.wp_proof (wp_confsAfterCount : confsAfterCount.spec (GF := GF) (hG := hG)) :
    State.OneWaiting.spec (GF := GF) (hG := hG) := by
  intro p s i sl l b
  wp_start as ⟨#Hs, #Hl, %Hi0, %Hi1, %Hb, %Hc, %Hlen⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases State.OneWaiting_intsRO_at g.ConfAt' s.confAt i ⟨Hi0, by rw [HWf.len_confAt]; exact Hi1⟩ $$ HConfAt with ⟨%w, #Hwa, %Hw⟩
  unfold State.oneWaiting at Hb
  cases hc : confsAfterCount l s.confAt[sint.nat i]! with
  | error _ => rw [hc] at Hb; cases Hb
  | ok n =>
  rw [hc] at Hb
  wp_auto
  wp_apply wp_load_at _ _ w Hi0 $$ [Hwa]
  · iexact Hwa
  try wp_auto
  wp_apply wp_confsAfterCount sl l w n $$ [Hl] as %r %Hr
  · iframe Hl; ipureintro; rw [Hw]; exact ⟨hc, by omega, Hlen⟩
  try wp_auto
  have hb : b = decide (n ≤ 1) := by
    have := Except.ok.inj Hb; exact this.symm
  have : decide (sint.Z r ≤ sint.Z (W64 1)) = b := by
    rw [hb, show sint.Z (W64 1) = 1 from rfl, Hr]
    simp only [decide_eq_decide]
    omega
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
