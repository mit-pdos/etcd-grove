/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Server__equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server__equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Config__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Durable__equal

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

-- A failing comparison: `false` (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "eq_fail" h:ident : tactic => `(tactic| (
    try wp_auto
    have hf : v.eq w srv = false := by simp [Server.eq, $h:ident]
    rw [hf]; iapply HΦ; ipureintro; trivial))

theorem Server.equal.wp_proof (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_SetEqual : Set.Equal.spec (GF := GF) (hG := hG))
    (wp_ConfigEqual : Config.Equal.spec (GF := GF) (hG := hG))
    (wp_DurableEqual : Durable.equal.spec (GF := GF) (hG := hG)) :
    Server.equal.spec (GF := GF) (hG := hG) := by
  intro p v q w sl srv
  wp_start as ⟨#Hv, #Hw, #Hs⟩
  iunfold serverRO at Hv Hw
  icases Hv with ⟨%gv, %mv, #Hpv, %Hfv, #Hlv, #Hrv, #Hgv, #Hmv, %Hmiv, #Hcv, #Hdv⟩
  icases Hw with ⟨%gw, %mw, #Hpw, %Hfw, #Hlw, #Hrw, #Hgw, #Hmw, %Hmiw, #Hcw, #Hdw⟩
  icases typedPointsto_split _ _ _ $$ Hpv with Hpvf
  icases typedPointsto_split _ _ _ $$ Hpw with Hpwf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpvf with ⟨#V1, #V2, #V3, #V4, #V5, #V6, #V7, #V8, #V9, #V10, #V11, #V12, -⟩
  icases Hpwf with ⟨#W1, #W2, #W3, #W4, #W5, #W6, #W7, #W8, #W9, #W10, #W11, #W12, -⟩
  wp_auto
  have e1 := sint_eq_iff _ _ _ _ Hfv.1 Hfw.1
  have e2 := strRel_eq_iff Hfv.2.1 Hfw.2.1
  have e3 := uint_eq_iff _ _ _ _ Hfv.2.2.1 Hfw.2.2.1
  have e4 := uint_eq_iff _ _ _ _ Hfv.2.2.2.1 Hfw.2.2.2.1
  have e5 := sint_eq_iff _ _ _ _ Hfv.2.2.2.2.1 Hfw.2.2.2.2.1
  have e6 := sint_eq_iff _ _ _ _ Hfv.2.2.2.2.2 Hfw.2.2.2.2.2
  by_cases h1 : v.currentTerm = w.currentTerm
  rotate_left
  · rw [decide_eq_false (fun x => h1 (e1.1 x))]; eq_fail h1
  rw [decide_eq_true (e1.2 h1)]
  wp_auto
  by_cases h2 : v.state = w.state
  rotate_left
  · rw [decide_eq_false (fun x => h2 (e2.1 x))]; eq_fail h2
  rw [decide_eq_true (e2.2 h2)]
  wp_auto
  by_cases h3 : v.votedFor = w.votedFor
  rotate_left
  · rw [decide_eq_false (fun x => h3 (e3.1 x))]; eq_fail h3
  rw [decide_eq_true (e3.2 h3)]
  wp_auto
  by_cases h4 : v.lead = w.lead
  rotate_left
  · rw [decide_eq_false (fun x => h4 (e4.1 x))]; eq_fail h4
  rw [decide_eq_true (e4.2 h4)]
  wp_auto
  by_cases h5 : v.commitIndex = w.commitIndex
  rotate_left
  · rw [decide_eq_false (fun x => h5 (e5.1 x))]; eq_fail h5
  rw [decide_eq_true (e5.2 h5)]
  wp_auto
  by_cases h6 : v.pendingConfChangeIndex = w.pendingConfChangeIndex
  rotate_left
  · rw [decide_eq_false (fun x => h6 (e6.1 x))]; eq_fail h6
  rw [decide_eq_true (e6.2 h6)]
  wp_auto
  wp_apply wp_EntriesEqual _ _ _ _ $$ [Hlv Hlw] as -
  · iframe Hlv Hlw
  by_cases h7 : v.log = w.log
  rotate_left
  · rw [decide_eq_false h7]; eq_fail h7
  rw [decide_eq_true h7]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  wp_auto
  wp_apply wp_SetEqual _ _ _ _ $$ [Hrv Hrw] as -
  · iframe Hrv Hrw
  by_cases h8 : v.votesResponded = w.votesResponded
  rotate_left
  · rw [decide_eq_false h8]; eq_fail h8
  rw [decide_eq_true h8]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  wp_auto
  wp_apply wp_SetEqual _ _ _ _ $$ [Hgv Hgw] as -
  · iframe Hgv Hgw
  by_cases h9 : v.votesGranted = w.votesGranted
  rotate_left
  · rw [decide_eq_false h9]; eq_fail h9
  rw [decide_eq_true h9]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Config.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  wp_auto
  wp_apply wp_ConfigEqual _ _ _ _ $$ [Hcv Hcw] as -
  · iframe Hcv Hcw
  by_cases h10 : v.config = w.config
  rotate_left
  · rw [decide_eq_false h10]; eq_fail h10
  rw [decide_eq_true h10]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Durable.TypeAssumptions.ptr_equal_unfold.method_unfold]
  wp_auto
  wp_apply wp_DurableEqual _ _ _ _ $$ [Hdv Hdw] as -
  · iframe Hdv Hdw
  by_cases h11 : v.durable = w.durable
  rotate_left
  · rw [decide_eq_false h11]; eq_fail h11
  rw [decide_eq_true h11]
  wp_auto
  iunfold setRO at Hs
  icases Hs with ⟨%xs, #Hxs, %Hxm⟩
  ihave %Hxl := ownSlice_len $$ Hxs
  have hfields : v.currentTerm == w.currentTerm && v.state == w.state && v.votedFor == w.votedFor &&
      v.lead == w.lead && v.commitIndex == w.commitIndex &&
      v.pendingConfChangeIndex == w.pendingConfChangeIndex && v.log == w.log &&
      v.votesResponded == w.votesResponded && v.votesGranted == w.votesGranted &&
      v.config == w.config && v.durable == w.durable := by
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have heq : v.eq w srv = srv.all (fun j => v.matchIndex j == w.matchIndex j) := by
    unfold Server.eq; rw [hfields, Bool.true_and]
  rw [heq]
  ihave IH : iprop(∃ (n jv : w64),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        (srv.take (sint.nat n)).all (fun j => v.matchIndex j == w.matchIndex j) = true⌝) $$ [i j]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hna⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hxl.1]; word
    obtain ⟨x, Hx⟩ : ∃ x, xs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsx : srv[sint.nat n]? = some (uint.nat x) := by rw [← Hxm, List.getElem?_map, Hx]; rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard x hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hx
    try wp_auto
    wp_apply wp_map_lookup1 $$ [Hmv] as -
    · iexact Hmv
    wp_apply wp_map_lookup1 $$ [Hmw] as -
    · iexact Hmw
    have hm := sint_eq_iff _ _ _ _ (Hmiv x) (Hmiw x)
    have htake : (srv.take (sint.nat (n + W64 1))).all (fun j => v.matchIndex j == w.matchIndex j) =
        ((srv.take (sint.nat n)).all (fun j => v.matchIndex j == w.matchIndex j) &&
          (v.matchIndex (uint.nat x) == w.matchIndex (uint.nat x))) := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hsx]
      simp
    rw [show (zero_val w64 : w64) = W64 0 from rfl]
    try wp_auto
    by_cases hx : v.matchIndex (uint.nat x) = w.matchIndex (uint.nat x)
    · rw [decide_eq_true (hm.2 hx)]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake, hna]; simpa using hx
    · rw [decide_eq_false (fun e => hx (hm.1 e))]
      try wp_auto
      wp_for_post
      try wp_auto
      have : srv.all (fun j => v.matchIndex j == w.matchIndex j) = false :=
        List.all_eq_false.2 ⟨uint.nat x, List.mem_of_getElem? Hsx, by simpa using hx⟩
      rw [this]
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have hnx : sint.nat n = srv.length := by rw [← Hxm, List.length_map, Hxl.1]; word
    rw [hnx, List.take_length] at hna
    rw [hna]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
