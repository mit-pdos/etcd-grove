/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__skipUnusedLogline`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__skipUnusedLogline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__isBecomeFollowerInUpdateTermOrReturnToFollower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

-- The message check of `skipUnusedLogline`'s first two disjuncts, once the event matched (hygiene off).
set_option hygiene false in
local macro "sk_norm" : tactic => `(tactic| (
  try wp_auto
  try rw [decide_eq_false Hgmnn]
  try simp only [Bool.not_false]
  try wp_auto
  try rw [decide_strRel Hgm.2.2.1 Hgm.2.2.2.1]
  try simp only [hft, _root_.decide_true, _root_.decide_false, Bool.not_true, Bool.not_false]
  try wp_auto))

-- The last disjunct (hygiene off).
set_option hygiene false in
local macro "sk_D" "[" xs:ident,* "]" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_loglineIsEvent t tr g ts go!"ReduceNextIndex" "ReduceNextIndex" $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  try wp_auto
  iapply HΦ'; ipureintro
  cases hD : tr.isEvent ts "ReduceNextIndex" <;> simp [Trace.skipUnusedLogline, hD, $[$xs:ident],*]))

-- The third disjunct, then the last (hygiene off).
set_option hygiene false in
local macro "sk_C" "[" xs:ident,* "]" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_isBF t tr g ts $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact Hl1
  cases hC : tr.isBecomeFollowerInUpdateTermOrReturnToFollower ts
  · sk_D [hC, $[$xs:ident],*]
  try wp_auto
  iapply HΦ'; ipureintro; simp [Trace.skipUnusedLogline, hC]))

-- The second disjunct, then the others (hygiene off).
set_option hygiene false in
local macro "sk_B" "[" xs:ident,* "]" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_loglineIsEvent t tr g ts go!"SendRequestVoteResponse" "SendRequestVoteResponse" $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hB : tr.isEvent ts "SendRequestVoteResponse"
  · sk_C [hB, $[$xs:ident],*]
  sk_norm
  first
    | (iapply HΦ'; ipureintro; simp [Trace.skipUnusedLogline, hB, $[$xs:ident],*]; done)
    | sk_C [hB, $[$xs:ident],*]))

-- All four (hygiene off).
set_option hygiene false in
local macro "sk_A" "[" xs:ident,* "]" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_loglineIsEvent t tr g ts go!"SendAppendEntriesResponse" "SendAppendEntriesResponse" $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hA : tr.isEvent ts "SendAppendEntriesResponse"
  · sk_B [hA, $[$xs:ident],*]
  sk_norm
  first
    | (iapply HΦ'; ipureintro; simp [Trace.skipUnusedLogline, hA, $[$xs:ident],*]; done)
    | sk_B [hA, $[$xs:ident],*]))

theorem Trace.skipUnusedLogline.wp_proof (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_loglineIsEvent : Trace.loglineIsEvent.spec (GF := GF) (hG := hG))
    (wp_isBF : Trace.isBecomeFollowerInUpdateTermOrReturnToFollower.spec (GF := GF) (hG := hG)) :
    Trace.skipUnusedLogline.spec (GF := GF) (hG := hG) := by
  intro t tr g ts
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hl2⟩
  ihave HΦ' : (∀ b : Bool, ⌜b = tr.skipUnusedLogline ts⌝ -∗ Φ #b) $$ [HΦ]
  · iintro %b %hb; rw [hb]; iapply HΦ; ipureintro; trivial
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
  open_lineP
  cases hm : (tr.line ts.l).ev.msg with
  | none =>
    icases Hemsg with %Hnull
    rw [Hnull]
    have Hgmnn : True := trivial
    have Hgm : True := trivial
    have hft : True := trivial
    sk_A [hm]
  | some m =>
    icases Hemsg with ⟨%gm, #Hgmp, %Hgm⟩
    ihave %Hgmnn := typedPointsto_not_null _ _ _ $$ Hgmp
    icases typedPointsto_split _ _ _ $$ Hgmp with Hgmf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hgmf with ⟨-, -, #GF3, #GF4, -⟩
    by_cases hft : m.from = m.to
    · sk_A [hm, hft]
    · sk_A [hm, hft]

end proof

end Etcdraft
end EtcdGrove
end Perennial
