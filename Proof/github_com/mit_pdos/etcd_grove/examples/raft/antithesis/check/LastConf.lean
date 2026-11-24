/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `LastConf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.LastConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsConf

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

/-- The step of `lastConf`'s fold. -/
def LastConf_f (l : List Entry) : Int → Nat → EvalM Int := fun last (i : Nat) => do
  let e ← atE l ((i : Int) + 1); pure (if isConf e then ((i + 1 : Nat) : Int) else last)

theorem LastConf_eq (l : List Entry) (a : Int) :
    lastConf l a = (List.range a.toNat).foldlM (LastConf_f l) 0 := rfl

theorem LastConf_arith (kv a : w64) (ha : sint.Z a < 2 ^ 63 - 1) (hq0 : 1 ≤ sint.Z kv) (hqk : sint.Z kv ≤ sint.Z a) :
    sint.nat (kv + W64 1) - 1 = (sint.nat kv - 1) + 1 ∧
      (sint.Z a).toNat - (sint.nat kv - 1) = ((sint.Z a).toNat - (sint.nat kv - 1) - 1) + 1 ∧
      (sint.Z a).toNat - (sint.nat kv - 1 + 1) = (sint.Z a).toNat - (sint.nat kv - 1) - 1 ∧
      sint.Z (kv + W64 1) = sint.Z kv + 1 ∧ ((sint.nat kv - 1 : Nat) : Int) + 1 = sint.Z kv ∧
      (((sint.nat kv - 1 + 1 : Nat) : Int)) = sint.Z kv := by
  refine ⟨by word, by word, by word, by word, by word, by word⟩

theorem LastConf_natZ (x : w64) (h : 0 ≤ sint.Z x) : (sint.nat x : Int) = sint.Z x := by word

theorem LastConf.wp_proof (wp_At : At.spec (GF := GF) (hG := hG)) (wp_IsConf : IsConf.spec (GF := GF) (hG := hG)) :
    LastConf.spec (GF := GF) (hG := hG) := by
  intro sl l a k
  wp_start as ⟨#Hl, %Hk, %Ha⟩
  rw [LastConf_eq] at Hk
  wp_auto
  ihave IH : iprop(∃ (kv lv : w64),
      "k" ∷ k_ptr ↦ kv ∗ "last" ∷ last_ptr ↦ lv ∗
      "%Hq" ∷ ⌜1 ≤ sint.Z kv ∧ (sint.Z kv ≤ sint.Z a + 1 ∨ sint.Z kv = 1) ∧
        (List.range' (sint.nat kv - 1) ((sint.Z a).toNat - (sint.nat kv - 1))).foldlM
          (LastConf_f l) (sint.Z lv) = .ok k⌝)
      $$ [k last]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by rw [show sint.Z (W64 1) = 1 from rfl]; omega, Or.inr rfl, ?_⟩
    rw [show sint.nat (W64 1) - 1 = 0 from rfl, Nat.sub_zero, ← List.range_eq_range']
    exact Hk
  wp_for IH
  obtain ⟨hq0, hq1, hqb⟩ := Hq
  wp_if_destruct
  · obtain ⟨hn1, hn2, hn3, hpq1, hqi, hqi'⟩ := LastConf_arith kv a Ha hq0 Hif
    rw [hn2, List.range'_succ, List.foldlM_cons] at hqb
    cases hx : atE l (sint.Z kv) with
    | error err =>
      have : LastConf_f l (sint.Z lv) (sint.nat kv - 1) = .error err := by
        unfold LastConf_f; rw [hqi, hx]; rfl
      rw [this] at hqb; cases hqb
    | ok x =>
    have hf : LastConf_f l (sint.Z lv) (sint.nat kv - 1) =
        .ok (if isConf x then sint.Z kv else sint.Z lv) := by
      unfold LastConf_f; rw [hqi, hx, hqi']; rfl
    rw [hf] at hqb
    have hqb' : List.foldlM (LastConf_f l) (if isConf x then sint.Z kv else sint.Z lv)
        (List.range' (sint.nat kv - 1 + 1) ((sint.Z a).toNat - (sint.nat kv - 1) - 1)) = Except.ok k := hqb
    wp_apply wp_At sl l kv x $$ [Hl] as %e #He
    · iframe Hl; ipureintro; exact hx
    try wp_auto
    wp_apply wp_IsConf e x $$ [He]
    · iexact He
    try wp_auto
    cases hc : isConf x
    · rw [hc] at hqb'
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by omega, by left; omega, ?_⟩
      rw [hn1, hn3]; exact hqb'
    · rw [hc] at hqb'
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by omega, by left; omega, ?_⟩
      rw [hn1, hn3]; exact hqb'
  · try wp_auto
    have h0 : (sint.Z a).toNat - (sint.nat kv - 1) = 0 := by
      have e1 := LastConf_natZ kv (by omega)
      omega
    rw [h0] at hqb
    cases Except.ok.inj hqb
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
