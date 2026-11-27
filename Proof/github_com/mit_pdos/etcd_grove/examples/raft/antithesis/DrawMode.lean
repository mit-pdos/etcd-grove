/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/DrawMode.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrawMode
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.coin
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.may

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

local notation "MM" => github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Mode.mk

theorem lit3_size (a b c : val) :
    go.arrayLiteralSize [KeyedElement none (ElementExpression go.uint64 a),
      KeyedElement none (ElementExpression go.uint64 b),
      KeyedElement none (ElementExpression go.uint64 c)] = 3 := rfl

theorem lit3_get (a b c r : w64) (hr : uint.Z r < uint.Z (W64 3)) :
    ∃ x, [a, b, c][(sint.Z r).toNat]? = some x ∧ (x = a ∨ x = b ∨ x = c) := by
  have : r = W64 0 ∨ r = W64 1 ∨ r = W64 2 := by
    by_cases h0 : uint.Z r = 0
    · left; word
    by_cases h1 : uint.Z r = 1
    · right; left; word
    right; right; have : uint.Z r < 3 := hr; word
  rcases this with rfl | rfl | rfl
  · exact ⟨a, rfl, Or.inl rfl⟩
  · exact ⟨b, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨c, rfl, Or.inr (Or.inr rfl)⟩

theorem inScope_of (s : H.Scope) (N V mi ms dl sp an : w64)
    (bt pv cq sd fw ay ba pa rd tr cc sn ss rs : Bool)
    (hn : N = W64 3 ∨ N = W64 5) (HV : V = N ∨ (s.NonVoters' = true ∧ N = W64 5 ∧ V = W64 3))
    (hbt : bt = true → s.Boot' = true) (hpv : pv = true → s.PreVote' = true)
    (hcq : cq = true → s.CheckQuorum' = true)
    (Hlim : if s.Limits' = true then (mi = W64 1 ∨ mi = W64 2 ∨ mi = W64 256) ∧
        (ms = W64 0 ∨ ms = W64 64 ∨ ms = W64 (2 ^ 20))
      else mi = W64 256 ∧ ms = W64 (2 ^ 20))
    (hfw : fw = true → s.Forwarding' = true) (Hdl : dl = W64 1 ∨ (s.Dup' = true ∧ dl = W64 2))
    (hay : ay = true → s.Async' = true) (hba : ba = true → s.Batch' = true)
    (Hps : (pa = true → s.Parallel' = true ∧ ay = false ∧ ba = false) ∧
        (sp = W64 0 ∨ (s.Split' = true ∧ ay = false ∧ ba = false ∧ sp = W64 1)))
    (hrd : rd = true → s.Reads' = true) (htr : tr = true → s.Transfer' = true)
    (hrs : rs = true → s.Restarts' = true) (hsn : sn = true → s.Snapshots' = true)
    (hcc : cc = true → s.ConfChanges' = true) (hss : ss = true → sn = true)
    (hsd : sd = true → cc = true) (han : 1 ≤ uint.Z an ∧ uint.Z an ≤ uint.Z V) :
    InScope s (MM N V bt pv cq sd mi ms fw dl ay ba pa sp rd tr cc sn ss rs an) := by
  unfold InScope
  refine ⟨hn, HV, hbt, hpv, hcq, ?_, hfw, Hdl, hay, hba, Hps.1, Hps.2, hrd, htr, hrs, hsn, hcc, hss, hsd,
    han.1, han.2⟩
  exact Hlim

local notation "splitTE" => github_com.mit_pdos.etcd_grove.examples.raft.antithesis.splitTermEntriesCommit

set_option hygiene false in
/-- Closes a join's case: the mode's cell, up to the literals' forms, and the pure facts. -/
local macro "jclose" : tactic => `(tactic| (iexists _; isplitl [s]; (· iexact s); isplitl [m]; (· iExactEq m; rfl); ipureintro))
set_option hygiene false in
/-- `jclose` for two witnesses. -/
local macro "jclose2" : tactic => `(tactic| (iexists _, _; isplitl [s]; (· iexact s); isplitl [m]; (· iExactEq m; rfl); ipureintro))

theorem DrawMode.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_coin : coin.spec (GF := GF) (hG := hG)) (wp_may : may.spec (GF := GF) (hG := hG)) :
    DrawMode.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_apply wp_below (W64 2) (by decide) as %r1 %hr1
  try wp_auto
  dsimp only
  have hn : W64 3 + W64 2 * r1 = W64 3 ∨ W64 3 + W64 2 * r1 = W64 5 := by
    have : r1 = W64 0 ∨ r1 = W64 1 := by
      have : uint.Z r1 < 2 := hr1
      by_cases h : uint.Z r1 = 0
      · left; word
      · right; word
    rcases this with rfl | rfl <;> decide
  generalize W64 3 + W64 2 * r1 = N at *
  wp_join (iprop(∃ V : w64, s_ptr ↦ s ∗ m_ptr ↦ (MM N V false false false false (W64 256) (W64 1048576) false (W64 1)
      false false false (W64 0) false false false false false false (W64 0)) ∗
      ⌜V = N ∨ (s.NonVoters' = true ∧ N = W64 5 ∧ V = W64 3)⌝)) with [m s]
  · wp_apply wp_may as %b %hb
    wp_if_destruct
    · wp_join_done; jclose; simp_all
    · wp_join_done; jclose; simp_all
  · jclose; simp_all
  iintro ⟨%V, s, m, %HV⟩
  wp_auto
  wp_apply wp_may as %bt %hbt
  try wp_auto
  wp_apply wp_may as %pv %hpv
  wp_apply wp_may as %cq %hcq
  try wp_auto
  dsimp only
  generalize hL : s.Limits' = L
  wp_join (iprop(∃ mi ms : w64, s_ptr ↦ s ∗ m_ptr ↦ (MM N V bt pv cq false mi ms false (W64 1)
      false false false (W64 0) false false false false false false (W64 0)) ∗
      ⌜if L then (mi = W64 1 ∨ mi = W64 2 ∨ mi = W64 256) ∧
        (ms = W64 0 ∨ ms = W64 64 ∨ ms = W64 (2 ^ 20))
      else mi = W64 256 ∧ ms = W64 (2 ^ 20)⌝)) with [m s]
  · jclose2; exact ⟨rfl, rfl⟩
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    try wp_auto
    wp_apply wp_below (W64 3) (by decide) as %r2 %hr2
    try wp_auto
    simp only [lit3_size]
    obtain ⟨x, hx1, hx2⟩ := lit3_get (W64 1) (W64 2) (W64 256) r2 hr2
    have hb : 0 ≤ sint.Z r2 ∧ sint.Z r2 < sint.Z (W64 3) := by
      have : uint.Z r2 < 3 := hr2; constructor <;> word
    simp only [hb, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z r2) [W64 1, W64 2, W64 256] (DFrac.own 1) x (by word) $$ [Hsl1] as -
    · isplitl [Hsl1]; (· iExactEq Hsl1; rfl); ipureintro; exact hx1
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    try wp_auto
    wp_apply wp_below (W64 3) (by decide) as %r3 %hr3
    try wp_auto
    simp only [lit3_size]
    obtain ⟨y, hy1, hy2⟩ := lit3_get (W64 0) (W64 64) (W64 1048576) r3 hr3
    have hb3 : 0 ≤ sint.Z r3 ∧ sint.Z r3 < sint.Z (W64 3) := by
      have : uint.Z r3 < 3 := hr3; constructor <;> word
    simp only [hb3, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z r3) [W64 0, W64 64, W64 1048576] (DFrac.own 1) y (by word) $$ [Hsl2] as -
    · isplitl [Hsl2]; (· iExactEq Hsl2; rfl); ipureintro; exact hy1
    try wp_auto
    wp_join_done
    jclose2
    exact ⟨hx2, hy2⟩
  iintro ⟨%mi, %ms, s, m, %Hlim⟩
  wp_auto
  wp_apply wp_may as %fw %hfw
  try wp_auto
  dsimp only
  wp_join (iprop(∃ dl : w64, s_ptr ↦ s ∗ m_ptr ↦ (MM N V bt pv cq false mi ms fw dl
      false false false (W64 0) false false false false false false (W64 0)) ∗
      ⌜dl = W64 1 ∨ (s.Dup' = true ∧ dl = W64 2)⌝)) at next with [m s]
  · wp_apply wp_may as %b %hb
    wp_if_destruct
    · wp_join_done; jclose; left; rfl
    · wp_join_done; jclose; right; exact ⟨hb rfl, rfl⟩
  iintro ⟨%dl, s, m, %Hdl⟩
  wp_auto
  wp_apply wp_may as %ay %hay
  wp_apply wp_may as %ba %hba
  try wp_auto
  dsimp only
  wp_join (iprop(∃ (pa : Bool) (sp : w64), s_ptr ↦ s ∗ m_ptr ↦ (MM N V bt pv cq false mi ms fw dl
      ay ba pa sp false false false false false false (W64 0)) ∗
      ⌜(pa = true → s.Parallel' = true ∧ ay = false ∧ ba = false) ∧
        (sp = W64 0 ∨ (s.Split' = true ∧ ay = false ∧ ba = false ∧ sp = W64 1))⌝)) at next with [m s]
  · cases ay <;> cases ba
    · try wp_auto
      wp_apply wp_may as %p %hp
      try wp_auto
      wp_apply wp_may as %q %hq
      try wp_auto
      wp_if_destruct
      all_goals ((try wp_auto); (try rw [show splitTE = #(W64 1) from rfl]); (try wp_auto); (try wp_join_done); jclose2)
      all_goals exact ⟨fun h => ⟨hp h, by trivial, by trivial⟩,
        by first | exact Or.inl rfl | exact Or.inr ⟨hq rfl, by trivial, by trivial, rfl⟩⟩
    all_goals ((try wp_auto); (try wp_join_done); jclose2; exact ⟨fun h => (nomatch h), Or.inl rfl⟩)
  iintro ⟨%pa, %sp, s, m, %Hps⟩
  wp_auto
  wp_apply wp_may as %rd %hrd
  wp_apply wp_may as %tr %htr
  wp_apply wp_may as %rs %hrs
  try wp_auto
  wp_apply wp_may as %sn %hsn
  wp_apply wp_may as %cc %hcc
  try wp_auto
  dsimp only
  have hVb : 0 < uint.Z V ∧ uint.Z V ≤ 5 := by
    rcases HV with rfl | ⟨_, _, rfl⟩
    · rcases hn with rfl | rfl <;> decide
    · decide
  subst hL
  cases sn <;> cases cc
  all_goals
    try wp_auto
    (try wp_apply wp_coin as %c1 _)
    try wp_auto
    (try wp_apply wp_coin as %c2 _)
    try wp_auto
    wp_apply wp_below V hVb.1 as %r4 %hr4
    try wp_auto
    iapply HΦ
    ipureintro
    apply inScope_of <;> first | assumption | (intro h; contradiction) | (intro _; rfl) | skip
    have : uint.Z r4 < 5 := by omega
    constructor <;> word

end proof

end AntHarness
end EtcdGrove
end Perennial
