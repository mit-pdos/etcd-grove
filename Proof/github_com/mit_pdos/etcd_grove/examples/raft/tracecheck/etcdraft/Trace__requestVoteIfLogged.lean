/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__requestVoteIfLogged`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__requestVoteIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__loglineIsMessageEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePostStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__RequestVote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__RequestPreVote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.nonNil
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.newPending
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isRequestVoteRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isRequestVoteResponse

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

set_option hygiene false in
/-- The enabled case (`hen`, `hle`): the line read, `RequestVote`, `RequestPreVote`, `nonNil`, the
loop over the successors. -/
local macro "rv_main" : tactic => `(tactic| (
  try simp only [Bool.not_true, Bool.not_false]
  try wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, hle⟩
  try wp_auto
  wp_apply wp_RequestVote g.S' ts.s i j $$ [Hst] as %q1 Hq1
  · iframe Hst; ipureintro; exact ⟨Hi, Hok⟩
  try wp_auto
  wp_apply wp_RequestPreVote g.S' ts.s i j $$ [Hst] as %q2 Hq2
  · iframe Hst; ipureintro; exact ⟨Hi, Hpv⟩
  try wp_auto
  wp_apply wp_slice_literal [q1, q2]
  isplitr
  · ipureintro; rfl
  iintro %sl0 ⟨Hsl0, -⟩
  try wp_auto
  wp_apply wp_nonNil _ (DFrac.own 1) [q1, q2]
      [ts.s.requestVote (uint.nat i) (uint.nat j), ts.s.requestPreVote (uint.nat i) (uint.nat j)]
      (fun p s => stateRO (GF := GF) p s) $$ [Hsl0 Hq1 Hq2] as %rs ⟨%qs, Hqs, Hqcap, #Hqrl⟩
  · iframe Hsl0
    isplitl [Hq1 Hq2]
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hq1]
      · iexact Hq1
      iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hq2]
      · iexact Hq2
      iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    imodintro
    iintro %p0 %s0 Hs0
    iapply stateRO_not_null $$ Hs0
  try wp_auto
  ipersist ln
  ihave %Hqsl := ownSlice_len $$ Hqs
  ihave %Hqll := BigSepL2.bigSepL2_length $$ Hqrl
  ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n : w64) (x : Loc) (osl : GoSlice) (acc : List State) (gsl : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "s2" ∷ s2_ptr ↦ x ∗ "out" ∷ out_ptr ↦ osl ∗ "Hqs" ∷ rs ↦* qs ∗
      "Hout" ∷ osl ↦* gsl ∗ "Hcap" ∷ ownSliceCap Loc osl (DFrac.own 1) ∗
      "Hacc" ∷ ([∗list] r;s ∈ gsl;acc, stateRO (GF := GF) r s) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z rs.len ∧
        ((somes [ts.s.requestVote (uint.nat i) (uint.nat j), ts.s.requestPreVote (uint.nat i) (uint.nat j)]).take
          (sint.nat n)).filter F = acc⌝) $$ [i s2 out Hqs Hnil Hcap0]
  · iexists _, _, _, [], _
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hacc⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < qs.length := by clear hacc; rw [Hqsl.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, qs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, (somes [ts.s.requestVote (uint.nat i) (uint.nat j), ts.s.requestPreVote (uint.nat i) (uint.nat j)])[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem (Hqll ▸ Hlt)⟩
    ihave #Hyx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => stateRO (GF := GF) a b) Hy Hx $$ Hqrl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z rs.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) qs (DFrac.own 1) y hn0 $$ [Hqs] as Hqs
    · iframe Hqs; ipureintro; exact Hy
    try wp_auto
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hacc; word
    have htake : ((somes [ts.s.requestVote (uint.nat i) (uint.nat j), ts.s.requestPreVote (uint.nat i) (uint.nat j)]).take (sint.nat n + 1)).filter F = acc ++ [x].filter F := by
      rw [List.take_add_one, Hx, Option.toList_some, List.filter_append, hacc]
    wp_apply wp_validatePostStates t tr g ts y x i $$ [Ht Hts Hyx]
    · iframe Ht Hts Hyx; ipureintro; exact ⟨Hl1, hle⟩
    cases hv : tr.validatePostStates ts x (uint.nat i)
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, acc, gsl
      iframe
      ipureintro
      refine ⟨by clear hacc htake; word, by clear hacc htake; word, ?_⟩
      rw [hn1', htake]; simp [hF, hv]
    try wp_auto
    wp_apply wp_newPending g.S' ts.s y x _
        (fun m => (tr.line ts.l).isRequestVoteRequest m ||
          ((tr.line ts.l).isRequestVoteResponse m && m.source == m.dest)) $$ [Hst Hyx Hlp ln]
    · iframe Hst Hyx
      imodintro
      iintro %q' %m' %Φ'
      imodintro
      iintro #Hm' HΦ''
      wp_auto
      wp_apply wp_isRVReq ql (tr.line ts.l) q' m' $$ [Hm' Hlp]
      · iframe Hm' Hlp
      cases hr : (tr.line ts.l).isRequestVoteRequest m'
      · wp_auto
        wp_apply wp_isRVResp ql (tr.line ts.l) q' m' $$ [Hm' Hlp]
        · iframe Hm' Hlp
        cases hr2 : (tr.line ts.l).isRequestVoteResponse m'
        · wp_auto
          simp only [Bool.false_or, Bool.false_and]
          iapply HΦ''; ipureintro; trivial
        wp_auto
        iunfold msgRO at Hm'
        icases Hm' with ⟨%gm, #Hgm, %Hv, -⟩
        icases typedPointsto_split _ _ _ $$ Hgm with Hgmf
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hgmf
        wp_auto
        rw [uint_decide Hv.2.2.2.2.2.2.2.2.2.2.2.1 Hv.2.2.2.2.2.2.2.2.2.2.2.2]
        have e : (m'.source == m'.dest) = decide (m'.source = m'.dest) := by
          by_cases h : m'.source = m'.dest <;> simp [h]
        simp only [Bool.false_or, Bool.true_and, e]
        iapply HΦ''; ipureintro; trivial
      wp_auto
      simp only [Bool.true_or]
      iapply HΦ''; ipureintro; trivial
    cases hp : newPending ts.s x (fun m => (tr.line ts.l).isRequestVoteRequest m ||
        ((tr.line ts.l).isRequestVoteResponse m && m.source == m.dest))
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, acc, gsl
      iframe
      ipureintro
      refine ⟨by clear hacc htake; word, by clear hacc htake; word, ?_⟩
      rw [hn1', htake]; simp [hF, hv, hp]
    try wp_auto
    wp_apply wp_slice_literal [y]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s3 ⟨Hs3, Hcap3, -⟩
    · iframe
    try wp_auto
    ihave Hacc' : ([∗list] r;s ∈ gsl ++ [y];acc ++ [x], stateRO (GF := GF) r s) $$ [Hacc]
    · iapply BigSepL2.bigSepL2_snoc.2
      isplitl [Hacc]
      · iexact Hacc
      iexact Hyx
    wp_for_post
    iframe
    iexists _, _, _, acc ++ [x], gsl ++ [y]
    iframe
    ipureintro
    refine ⟨by clear hacc htake; word, by clear hacc htake; word, ?_⟩
    rw [hn1', htake]; simp [hF, hv, hp]
  · try wp_auto
    have hnx : sint.nat n = (somes [ts.s.requestVote (uint.nat i) (uint.nat j), ts.s.requestPreVote (uint.nat i) (uint.nat j)]).length := by clear hacc; rw [← Hqll, Hqsl.1]; word
    rw [hnx, List.take_length] at hacc
    ihave Hres : statesOut (GF := GF) osl acc $$ [Hout Hcap Hacc]
    · iunfold statesOut; iexists gsl; iframe
    iapply HΦ' $$ [] Hres
    ipureintro
    rw [← hacc, hF]
    unfold Trace.requestVoteIfLogged
    simp only [hen, Bool.not_true, Bool.false_eq_true, ite_false]))

theorem Trace.requestVoteIfLogged.wp_proof
    (wp_loglineIsMessageEvent : Trace.loglineIsMessageEvent.spec (GF := GF) (hG := hG))
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_validatePostStates : Trace.validatePostStates.spec (GF := GF) (hG := hG))
    (wp_RequestVote : State.RequestVote.spec (GF := GF) (hG := hG))
    (wp_RequestPreVote : State.RequestPreVote.spec (GF := GF) (hG := hG))
    (wp_nonNil : nonNil.spec (GF := GF) (hG := hG))
    (wp_newPending : newPending.spec (GF := GF) (hG := hG))
    (wp_isRVReq : line.isRequestVoteRequest.spec (GF := GF) (hG := hG))
    (wp_isRVResp : line.isRequestVoteResponse.spec (GF := GF) (hG := hG)) :
    Trace.requestVoteIfLogged.spec (GF := GF) (hG := hG) := by
  intro t tr g ts i j
  obtain ⟨F, hF⟩ : ∃ F : State → Bool, F = fun s2 => tr.validatePostStates ts s2 (uint.nat i) &&
      newPending ts.s s2 (fun m => (tr.line ts.l).isRequestVoteRequest m ||
        ((tr.line ts.l).isRequestVoteResponse m && m.source == m.dest)) := ⟨_, rfl⟩
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hi, %Hok, %Hpv⟩
  ihave HΦ' : (∀ out sts, ⌜sts = tr.requestVoteIfLogged ts (uint.nat i) (uint.nat j)⌝ -∗ statesOut out sts -∗ Φ #out) $$ [HΦ]
  · iintro %out %sts %hs Hout; rw [hs]; iapply HΦ $$ Hout
  open_ts
  wp_auto
  wp_apply wp_loglineIsMessageEvent t tr g ts go!"SendRequestVoteRequest" "SendRequestVoteRequest" i j $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
  cases hA : tr.isMessageEvent ts "SendRequestVoteRequest" (uint.nat i) (uint.nat j)
  · try wp_auto
    wp_apply wp_loglineIsMessageEvent t tr g ts go!"SendRequestVoteResponse" "SendRequestVoteResponse" i j $$ [Ht Hts]
    · iframe Ht Hts; ipureintro; exact ⟨by strRel_lit, Hl1⟩
    cases hB : tr.isMessageEvent ts "SendRequestVoteResponse" (uint.nat i) (uint.nat j)
    · ret_nil [Trace.requestVoteIfLogged, hA, hB]
    try wp_auto
    rw [uint_decide rfl rfl]
    by_cases hij : uint.nat i = uint.nat j
    rotate_left
    · rw [decide_eq_false hij]
      ret_nil [Trace.requestVoteIfLogged, hA, hB, hij]
    rw [decide_eq_true hij]
    have hle : ts.l ≤ tr.len := Trace.isMessageEvent_le hB
    have hen : (tr.isMessageEvent ts "SendRequestVoteRequest" (uint.nat i) (uint.nat j) ||
        (tr.isMessageEvent ts "SendRequestVoteResponse" (uint.nat i) (uint.nat j) && uint.nat i == uint.nat j)) = true := by
      rw [hB, hij]; simp
    rv_main
  · have hle : ts.l ≤ tr.len := Trace.isMessageEvent_le hA
    have hen : (tr.isMessageEvent ts "SendRequestVoteRequest" (uint.nat i) (uint.nat j) ||
        (tr.isMessageEvent ts "SendRequestVoteResponse" (uint.nat i) (uint.nat j) && uint.nat i == uint.nat j)) = true := by
      simp [hA]
    rv_main

end proof

end Etcdraft
end EtcdGrove
end Perennial
