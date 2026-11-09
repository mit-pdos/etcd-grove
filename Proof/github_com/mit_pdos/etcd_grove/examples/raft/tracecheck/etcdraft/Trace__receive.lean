/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__receive`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__receive
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__validatePreStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Receive
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Domain
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.oneLessMessage
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isAppendEntriesRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isAppendEntriesResponse
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

-- `continue`: the loop's next round, the accumulator unchanged (`hstep` with `hG0 : Gf acc x = .ok acc`).
set_option hygiene false in
local macro "rcv_skip" : tactic => `(tactic| (
  try wp_auto
  wp_for_post
  iframe
  iexists _, _, _, acc, gsl
  iframe
  ipureintro
  exact ⟨by clear hacc hstep; word, by clear hacc hstep; word, by rw [hn1']; exact hstep acc hG0⟩))

-- After the switch (`matches` holds `isM x`): the checks, `Receive`, its successors appended.
set_option hygiene false in
local macro "rcv_cont" : tactic => `(tactic| (
  try wp_auto
  cases hmx : isM x
  · have hG0 : Gf acc x = .ok acc := by rw [hG]; simp [hmx, Pure.pure, Except.pure]
    rcv_skip
  try wp_auto
  ihave #Hyx0 := Hyx
  iunfold msgRO at Hyx0
  icases Hyx0 with ⟨%gmx, #Hgmx, %Hvx, -⟩
  icases typedPointsto_split _ _ _ $$ Hgmx with Hgmxf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hgmxf with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #MD, -⟩
  try wp_auto
  wp_apply wp_validatePreStates t tr g ts gmx.Dest' $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
  rw [Hvx.2.2.2.2.2.2.2.2.2.2.2.2]
  cases hvp : tr.validatePreStates ts x.dest
  · have hG0 : Gf acc x = .ok acc := by rw [hG]; simp [hmx, hvp, Pure.pure, Except.pure]
    rcv_skip
  try wp_auto
  have Hxm : x ∈ ts.s.messages.domain := List.mem_of_getElem? Hx
  obtain ⟨hm1, hm2, hm3, hm4, hm5, hm6, hm7⟩ := Hms x Hxm
  wp_apply wp_Receive g.S' ts.s y x $$ [Hst Hyx] as %rsl Hrs
  · iframe Hst Hyx
    ipureintro; exact ⟨Hpok, Hmok, hm1, hm2, hm3, hm4, hm5, hm6, hm7⟩
  cases hrv : ts.s.receive x with
  | error err => icases Hrs with %Hf; exact absurd Hf id
  | ok sts2 =>
  icases Hrs with ⟨%rqs, Hrq, Hrcap, #Hrl⟩
  ihave %Hrql := ownSlice_len $$ Hrq
  ihave %Hrll := BigSepL2.bigSepL2_length $$ Hrl
  have hG1 : Gf acc x = .ok (acc ++ sts2.map (mk x)) := by
    rw [hG]; simp [hmx, hvp, hrv, Bind.bind, Except.bind, Pure.pure, Except.pure]
  ihave IH2 : iprop(∃ (k : w64) (z : Loc) (osl2 : GoSlice) (gsl2 : List G.TState),
      "i" ∷ i_ptr ↦ k ∗ "s2" ∷ s2_ptr ↦ z ∗ "out" ∷ out_ptr ↦ osl2 ∗ "Hout" ∷ osl2 ↦* gsl2 ∗
      "Hcap" ∷ ownSliceCap G.TState osl2 (DFrac.own 1) ∗
      "Hacc" ∷ ([∗list] g';a ∈ gsl2;acc ++ (sts2.take (sint.nat k)).map (mk x), tstateRO g' a) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z rsl.len⌝) $$ [i s2 out Hout Hcap Hacc]
  · iexists _, _, _, _
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH2
  obtain ⟨hk0, hk1⟩ := Hk
  wp_if_destruct
  · have Hlt2 : sint.nat k < rqs.length := by rw [Hrql.1]; word
    obtain ⟨q2, Hq2⟩ : ∃ q2, rqs[sint.nat k]? = some q2 := ⟨_, List.getElem?_eq_getElem Hlt2⟩
    obtain ⟨s2v, Hs2v⟩ : ∃ s2v, sts2[sint.nat k]? = some s2v :=
      ⟨_, List.getElem?_eq_getElem (Hrll ▸ Hlt2)⟩
    ihave #Hq2s := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => stateRO (GF := GF) a b) Hq2 Hs2v $$ Hrl
    try dsimp only
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rsl.len from ⟨hk0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z k) rqs (DFrac.own 1) q2 hk0 $$ [Hrq] as Hrq
    · iframe Hrq; ipureintro; exact Hq2
    try wp_auto
    wp_apply wp_oneLessMessage g.S' ts.s q2 s2v y x $$ [Hst Hq2s Hyx]
    · iframe Hst Hq2s Hyx
    have hk1' : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have htk : sts2.take (sint.nat k + 1) = sts2.take (sint.nat k) ++ [s2v] := by
      rw [List.take_add_one, Hs2v]; rfl
    have hlz : sint.Z (g.L' + W64 1) = (ts.l : Int) + 1 := by
      have : (ts.l : Int) + 1 < 2 ^ 63 := by unfold numBound at hlenb; omega
      rw [← Hg.1] at this ⊢; word
    cases hol : oneLessMessage ts.s s2v x
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl0 ⟨Hsl0, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s3 ⟨Hs3, Hcap3, -⟩
      · iframe
      try wp_auto
      ihave Hacc' : ([∗list] g';a ∈ gsl2 ++ [({ S' := q2, L' := g.L', PL' := g.L' } : G.TState)];
          acc ++ (sts2.take (sint.nat (k + W64 1))).map (mk x), tstateRO g' a) $$ [Hacc]
      · rw [hk1', htk, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
        iapply BigSepL2.bigSepL2_snoc.2
        isplitl [Hacc]
        · iexact Hacc
        iunfold tstateRO
        simp only [hmk, hol, Bool.false_eq_true, ite_false]
        isplitr
        · iexact Hq2s
        ipureintro
        exact ⟨Hg.1, Hg.1⟩
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; constructor <;> word
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl0 ⟨Hsl0, -⟩
      try wp_auto
      wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s3 ⟨Hs3, Hcap3, -⟩
      · iframe
      try wp_auto
      ihave Hacc' : ([∗list] g';a ∈ gsl2 ++ [({ S' := q2, L' := g.L' + W64 1, PL' := g.L' } : G.TState)];
          acc ++ (sts2.take (sint.nat (k + W64 1))).map (mk x), tstateRO g' a) $$ [Hacc]
      · rw [hk1', htk, List.map_append, List.map_cons, List.map_nil, ← List.append_assoc]
        iapply BigSepL2.bigSepL2_snoc.2
        isplitl [Hacc]
        · iexact Hacc
        iunfold tstateRO
        simp only [hmk, hol, ite_true]
        isplitr
        · iexact Hq2s
        ipureintro
        exact ⟨hlz, Hg.1⟩
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; constructor <;> word
  · try wp_auto
    have hkx : sint.nat k = sts2.length := by rw [← Hrll, Hrql.1]; word
    rw [hkx, List.take_length] at *
    wp_for_post
    iframe
    iexists _, _, _, acc ++ sts2.map (mk x), _
    iframe
    ipureintro
    exact ⟨by clear hacc hstep; word, by clear hacc hstep; word, by rw [hn1']; exact hstep _ hG1⟩))

set_option maxHeartbeats 1000000 in
theorem Trace.receive.wp_proof (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_validatePreStates : Trace.validatePreStates.spec (GF := GF) (hG := hG))
    (wp_Receive : State.Receive.spec (GF := GF) (hG := hG))
    (wp_Domain : Bag.Domain.spec (GF := GF) (hG := hG))
    (wp_oneLessMessage : oneLessMessage.spec (GF := GF) (hG := hG))
    (wp_isAER : line.isAppendEntriesRequest.spec (GF := GF) (hG := hG))
    (wp_isAEResp : line.isAppendEntriesResponse.spec (GF := GF) (hG := hG))
    (wp_isRVReq : line.isRequestVoteRequest.spec (GF := GF) (hG := hG))
    (wp_isRVResp : line.isRequestVoteResponse.spec (GF := GF) (hG := hG)) :
    Trace.receive.spec (GF := GF) (hG := hG) := by
  intro t tr g ts
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hl2, %Hpok, %Hmok, %Hms⟩
  open_ts
  ihave #Hpi := etcdraftInit_get $$ Hpkg
  icases Hpi with ⟨-, -, ⟨%mr, #Hmr, #Hrnm⟩⟩
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
  open_lineP
  wp_auto
  wp_apply wp_map_lookup1 $$ [Hrnm] as -
  · iexact Hrnm
  rw [show (zero_val Bool) = false from rfl, receiveNamesMap_lookup Hef.1]
  cases hrn : isReceiveName (tr.line ts.l).ev.name
  · wp_auto
    have : tr.receive ts = .ok [] := by
      unfold Trace.receive; simp [hrn, Pure.pure, Except.pure]
    rw [this]
    iapply HΦ
    iunfold tstatesOut
    iexists []
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iapply BigSepL2.bigSepL2_nil.2
    ipureintro; trivial
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql2 #Hlp2
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
  ihave #Hlp20 := Hlp2
  iunfold linePtrRO at Hlp20
  icases Hlp20 with ⟨%ln2, #Hq2, #Hln2⟩
  iunfold lineRO at Hln2
  icases Hln2 with ⟨⟨%ge2, #Hev2, #Hevr2⟩, -⟩
  iunfold eventRO at Hevr2
  icases Hevr2 with ⟨%Hef2, -⟩
  icases typedPointsto_split _ _ _ $$ Hq2 with Hq2f
  simp only [TypedPointsto.typedPointstoDef]
  icases Hq2f with ⟨#Q2ev, -⟩
  icases typedPointsto_split _ _ _ $$ Hev2 with Hev2f
  simp only [TypedPointsto.typedPointstoDef]
  icases Hev2f with ⟨#N2, -⟩
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%gs, %sm, #Hp, -, -, -, -, -, #Hmsgs, -, -⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨-, -, #PMs, -⟩
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Domain_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Domain gs.Messages' ts.s.messages $$ [Hmsgs] as %sl #Hsl
  · iexact Hmsgs
  iunfold msgsRO at Hsl
  icases Hsl with ⟨%ps, #Hps, #Hpl⟩
  ihave %Hlen := ownSlice_len $$ Hps
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hpl
  -- the Lean's fold
  obtain ⟨isM, hisM⟩ : ∃ isM : Msg → Bool, isM = fun m =>
      if Bool.or ((tr.line ts.l).ev.name == "ReceiveAppendEntriesRequest") ((tr.line ts.l).ev.name == "ReceiveSnapshot") then
        (tr.line ts.l).isAppendEntriesRequest m
      else if ((tr.line ts.l).ev.name == "ReceiveAppendEntriesResponse") then (tr.line ts.l).isAppendEntriesResponse m
      else if ((tr.line ts.l).ev.name == "ReceiveRequestVoteRequest") then (tr.line ts.l).isRequestVoteRequest m
      else (tr.line ts.l).isRequestVoteResponse m := ⟨_, rfl⟩
  obtain ⟨mk, hmk⟩ : ∃ mk : Msg → State → TState, mk = fun m s2 =>
      if oneLessMessage ts.s s2 m then { s := s2, l := ts.l + 1, pl := ts.l } else { s := s2, l := ts.l, pl := ts.l } :=
    ⟨_, rfl⟩
  obtain ⟨Gf, hG⟩ : ∃ Gf : List TState → Msg → EvalM (List TState), Gf = fun acc m => do
      if Bool.or (!isM m) (!tr.validatePreStates ts m.dest) then return acc
      let succ ← ts.s.receive m
      return acc ++ succ.map (mk m) := ⟨_, rfl⟩
  have hrecv : tr.receive ts = ts.s.messages.domain.foldlM Gf [] := by
    unfold Trace.receive
    rw [hG, hisM, hmk]
    simp only [hrn, Bool.not_true, Bool.false_eq_true, ite_false]
  ihave #Ht0 := Ht
  iunfold traceRO at Ht0
  icases Ht0 with ⟨%Hv, -⟩
  have hlenb : (tr.len : Int) < numBound := by
    obtain ⟨evs, -, hlt, hnt⟩ := Hv
    rw [newTraceWith_len evs false false tr hnt]; exact hlt
  ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List G.TState) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap G.TState (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n : w64) (x : Loc) (osl : GoSlice) (acc : List TState) (gsl : List G.TState),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ x ∗ "out" ∷ out_ptr ↦ osl ∗
      "Hout" ∷ osl ↦* gsl ∗ "Hcap" ∷ ownSliceCap G.TState osl (DFrac.own 1) ∗
      "Hacc" ∷ ([∗list] g';a ∈ gsl;acc, tstateRO g' a) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        (ts.s.messages.domain.take (sint.nat n)).foldlM Gf [] = .ok acc⌝) $$ [i m out Hnil Hcap0]
  · iexists _, _, _, [], _
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hacc⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by clear hacc; rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, ps[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, ts.s.messages.domain[sint.nat n]? = some x :=
      ⟨_, List.getElem?_eq_getElem (Hll ▸ Hlt)⟩
    ihave #Hyx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => msgRO (GF := GF) a b) Hy Hx $$ Hpl
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hacc; word
    have hstep : ∀ r, Gf acc x = .ok r →
        (ts.s.messages.domain.take (sint.nat n + 1)).foldlM Gf [] = .ok r := by
      intro r hr
      rw [List.take_add_one, Hx, Option.toList_some, List.foldlM_append, hacc]
      simp [Bind.bind, Except.bind, hr, Pure.pure, Except.pure]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) ps DFrac.discard y hn0 $$ [Hps] as -
    · isplitr
      · iexact Hps
      ipureintro; exact Hy
    try wp_auto
    rw [decide_strRel Hef2.1 (show strRel go!"ReceiveSnapshot" "ReceiveSnapshot" by strRel_lit)]
    by_cases e1 : (tr.line ts.l).ev.name = "ReceiveSnapshot"
    · rw [decide_eq_true e1]
      try wp_auto
      wp_apply wp_isAER ql2 (tr.line ts.l) y x $$ [Hlp2 Hyx]
      · iframe Hlp2 Hyx
      rw [show (tr.line ts.l).isAppendEntriesRequest x = isM x by rw [hisM]; simp [e1]]
      rcv_cont
    rw [decide_eq_false e1]
    try wp_auto
    rw [decide_strRel Hef2.1 (show strRel go!"ReceiveAppendEntriesRequest" "ReceiveAppendEntriesRequest" by strRel_lit)]
    by_cases e2 : (tr.line ts.l).ev.name = "ReceiveAppendEntriesRequest"
    · rw [decide_eq_true e2]
      try wp_auto
      wp_apply wp_isAER ql2 (tr.line ts.l) y x $$ [Hlp2 Hyx]
      · iframe Hlp2 Hyx
      rw [show (tr.line ts.l).isAppendEntriesRequest x = isM x by rw [hisM]; simp [e2]]
      rcv_cont
    rw [decide_eq_false e2]
    try wp_auto
    rw [decide_strRel Hef2.1 (show strRel go!"ReceiveAppendEntriesResponse" "ReceiveAppendEntriesResponse" by strRel_lit)]
    by_cases e3 : (tr.line ts.l).ev.name = "ReceiveAppendEntriesResponse"
    · rw [decide_eq_true e3]
      try wp_auto
      wp_apply wp_isAEResp ql2 (tr.line ts.l) y x $$ [Hlp2 Hyx]
      · iframe Hlp2 Hyx
      rw [show (tr.line ts.l).isAppendEntriesResponse x = isM x by rw [hisM]; simp [e1, e2, e3]]
      rcv_cont
    rw [decide_eq_false e3]
    try wp_auto
    rw [decide_strRel Hef2.1 (show strRel go!"ReceiveRequestVoteRequest" "ReceiveRequestVoteRequest" by strRel_lit)]
    by_cases e4 : (tr.line ts.l).ev.name = "ReceiveRequestVoteRequest"
    · rw [decide_eq_true e4]
      try wp_auto
      wp_apply wp_isRVReq ql2 (tr.line ts.l) y x $$ [Hlp2 Hyx]
      · iframe Hlp2 Hyx
      rw [show (tr.line ts.l).isRequestVoteRequest x = isM x by rw [hisM]; simp [e1, e2, e3, e4]]
      rcv_cont
    rw [decide_eq_false e4]
    try wp_auto
    rw [decide_strRel Hef2.1 (show strRel go!"ReceiveRequestVoteResponse" "ReceiveRequestVoteResponse" by strRel_lit)]
    by_cases e5 : (tr.line ts.l).ev.name = "ReceiveRequestVoteResponse"
    · rw [decide_eq_true e5]
      try wp_auto
      wp_apply wp_isRVResp ql2 (tr.line ts.l) y x $$ [Hlp2 Hyx]
      · iframe Hlp2 Hyx
      rw [show (tr.line ts.l).isRequestVoteResponse x = isM x by rw [hisM]; simp [e1, e2, e3, e4]]
      rcv_cont
    exfalso
    simp only [isReceiveName, Bool.or_eq_true, beq_iff_eq] at hrn
    rcases hrn with (((h | h) | h) | h) | h
    · exact e2 h
    · exact e3 h
    · exact e4 h
    · exact e5 h
    · exact e1 h
  · try wp_auto
    have hnx : sint.nat n = ts.s.messages.domain.length := by clear hacc; rw [← Hll, Hlen.1]; word
    rw [hnx, List.take_length] at hacc
    rw [hrecv, hacc]
    iapply HΦ
    iunfold tstatesOut
    iexists gsl
    iframe

end proof

end Etcdraft
end EtcdGrove
end Perennial
