/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__nonReceive`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__nonReceive
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__logline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__skipUnusedLogline
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__requestVoteIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__becomeLeaderIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__clientRequestIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__advanceCommitIndexIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__appendEntriesIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__heartbeatIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__appendEntriesToSelfIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__timeoutIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__preTimeoutIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__ignoreInLeaseIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__applySimpleConfChangeIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__readyIfLogged
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__stepDownToFollowerIfLogged

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
/-- After the switch: `SkipUnusedLogline`'s state appended where it applies, `out` returned
(`Hout`/`Hcap`/`Hacc` the successors so far, `hsts` the Lean's result over them). -/
local macro "nr_tail" : tactic => `(tactic| (
  wp_apply wp_skip t tr g ts $$ [Ht Hts]
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
  cases hsk : tr.skipUnusedLogline ts
  · wp_auto
    iapply HΦ
    rw [hsts, hsk]
    iunfold statesOut
    iexists gsl
    iframe
  · wp_auto
    wp_apply wp_slice_literal [g.S']
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s3 ⟨Hs3, Hcap3, -⟩
    · iframe
    try wp_auto
    iapply HΦ
    rw [hsts, hsk]
    simp only [↓reduceIte]
    iunfold statesOut
    iexists gsl ++ [g.S']
    iframe
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · iexact Hst
    iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial))

set_option hygiene false in
/-- A loop over the trace's servers appending `t.X(ts, i)`'s successors, `F i` (`tac` applies `X`'s spec,
naming its result `Hr : statesOut rsl (F (uint.nat y))`), then `nr_tail`. -/
local macro "srv_loop1" F:term "with" tac:tacticSeq : tactic => `(tactic| (
  rename_i iv_ptr
  irename : (iv_ptr ↦ (zero_val w64 : w64)) => iv
  ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n x : w64) (osl : GoSlice) (acc : List State) (gsl : List Loc),
      "iv" ∷ iv_ptr ↦ x ∗ "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ osl ∗
      "Hout" ∷ osl ↦* gsl ∗ "Hcap" ∷ ownSliceCap Loc osl (DFrac.own 1) ∗
      "Hacc" ∷ ([∗list] r;s ∈ gsl;acc, stateRO (GF := GF) r s) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gt.Server'.len ∧
        (tr.server.take (sint.nat n)).flatMap $F = acc⌝) $$ [iv i out Hnil Hcap0]
  · iexists _, _, _, [], _
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hacc⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by clear hacc; rw [Hxl.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hyS : uint.nat y ∈ ts.s.server := by
      rw [Hsv, ← Hxsm]; exact List.mem_map.2 ⟨y, List.mem_of_getElem? Hy, rfl⟩
    have hyT : tr.server[sint.nat n]? = some (uint.nat y) := by rw [← Hxsm, List.getElem?_map, Hy]; rfl
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hacc; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gt.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    ($tac)
    iunfold statesOut at Hr
    icases Hr with ⟨%rqs, Hrq, -, Hrl⟩
    ihave %Hal := BigSepL2.bigSepL2_length $$ Hacc
    wp_apply wp_slice_append $$ [Hout Hcap Hrq] as %s3 ⟨Hs3, Hcap3, -⟩
    · iframe
    try wp_auto
    ihave Hacc' : ([∗list] r;s ∈ gsl ++ rqs;acc ++ $F (uint.nat y), stateRO (GF := GF) r s)
        $$ [Hacc Hrl]
    · iapply (BigSepL2.bigSepL2_append (Or.inl Hal)).2
      iframe
    wp_for_post
    iframe
    iexists _, _, _, acc ++ $F (uint.nat y), gsl ++ rqs
    iframe
    ipureintro
    refine ⟨by clear hacc; word, by clear hacc; word, ?_⟩
    rw [hn1', List.take_add_one, hyT, ← hacc]; simp
  · try wp_auto
    have hnx : sint.nat n = tr.server.length := by clear hacc; rw [← Hxll, Hxl.1]; word
    rw [hnx, List.take_length, ← hout0] at hacc
    subst hacc
    nr_tail))

set_option hygiene false in
/-- A case of the switch on the line's name `X` (`nk` its hypothesis) whose body is a loop over the
servers (`srv_loop1 F with tac`); the other cases go on. -/
local macro "nr_case1" nk:ident "," gx:term "," X:str "," F:term "with" tac:tacticSeq : tactic => `(tactic| (
  rw [decide_strRel Hef.1 (show strRel $gx $X by strRel_lit)]
  by_cases $nk:ident : (tr.line ts.l).ev.name = $X
  · rw [decide_eq_true $nk:ident]
    obtain ⟨out0, hsts, hout0⟩ : ∃ out0, sts = (if tr.skipUnusedLogline ts then out0 ++ [ts.s] else out0) ∧
        out0 = tr.server.flatMap $F := by
      simp [Trace.nonReceive, $nk:ident, Bind.bind, Except.bind, Pure.pure, Except.pure] at Hnr
      exact ⟨_, Hnr.symm, rfl⟩
    wp_auto
    srv_loop1 $F with ($tac)
  rw [decide_eq_false $nk:ident]
  wp_auto))

set_option hygiene false in
/-- The `SendRequestVote*` case's body (`hout0` its Lean result): a loop over the servers `i` of a loop
over the servers `j` appending `t.requestVoteIfLogged(ts, i, j)`'s successors. -/
local macro "rv_body" : tactic => `(tactic| (
  wp_auto
  rename_i iv_ptr
  irename : (iv_ptr ↦ (zero_val w64 : w64)) => iv
  ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n x : w64) (osl : GoSlice) (acc : List State) (gsl : List Loc),
      "iv" ∷ iv_ptr ↦ x ∗ "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ osl ∗
      "Hout" ∷ osl ↦* gsl ∗ "Hcap" ∷ ownSliceCap Loc osl (DFrac.own 1) ∗
      "Hacc" ∷ ([∗list] r;s ∈ gsl;acc, stateRO (GF := GF) r s) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gt.Server'.len ∧
        (tr.server.take (sint.nat n)).flatMap
          (fun i => tr.server.flatMap (fun j => tr.requestVoteIfLogged ts i j)) = acc⌝) $$ [iv i out Hnil Hcap0]
  · iexists _, _, _, [], _
    iframe
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hacc⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by clear hacc; rw [Hxl.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hyS : uint.nat y ∈ ts.s.server := by
      rw [Hsv, ← Hxsm]; exact List.mem_map.2 ⟨y, List.mem_of_getElem? Hy, rfl⟩
    have hyT : tr.server[sint.nat n]? = some (uint.nat y) := by rw [← Hxsm, List.getElem?_map, Hy]; rfl
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hacc; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gt.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    ihave IH2 : iprop(∃ (m jv : w64) (osl2 : GoSlice) (acc2 : List State) (gsl2 : List Loc),
        "j" ∷ j_ptr ↦ jv ∗ "i" ∷ i_ptr ↦ m ∗ "out" ∷ out_ptr ↦ osl2 ∗
        "Hout" ∷ osl2 ↦* gsl2 ∗ "Hcap" ∷ ownSliceCap Loc osl2 (DFrac.own 1) ∗
        "Hacc" ∷ ([∗list] r;s ∈ gsl2;acc2, stateRO (GF := GF) r s) ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z gt.Server'.len ∧
          acc ++ (tr.server.take (sint.nat m)).flatMap (fun j => tr.requestVoteIfLogged ts (uint.nat y) j) = acc2⌝)
        $$ [j i out Hout Hcap Hacc]
    · iexists _, _, _, acc, gsl
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IH2
    obtain ⟨hm0, hm1, hacc2⟩ := Hm
    wp_if_destruct
    · have Hlt2 : sint.nat m < xs.length := by clear hacc2; rw [Hxl.1]; word
      obtain ⟨y2, Hy2⟩ : ∃ y2, xs[sint.nat m]? = some y2 := ⟨_, List.getElem?_eq_getElem Hlt2⟩
      have hyT2 : tr.server[sint.nat m]? = some (uint.nat y2) := by rw [← Hxsm, List.getElem?_map, Hy2]; rfl
      have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hacc2; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z gt.Server'.len from ⟨hm0, Hif⟩))]
      wp_apply wp_load_slice_index _ (sint.Z m) xs DFrac.discard y2 hm0 $$ [Hxs] as -
      · isplitr
        · iexact Hxs
        ipureintro; exact Hy2
      try wp_auto
      wp_apply wp_requestVote t tr g ts y y2 $$ [Ht Hts] as %rsl Hr
      · iframe Ht Hts; ipureintro; exact ⟨Hl1, hyS, Hact.2.2.1, Hact.1⟩
      iunfold statesOut at Hr
      icases Hr with ⟨%rqs, Hrq, -, Hrl⟩
      ihave %Hal := BigSepL2.bigSepL2_length $$ Hacc
      wp_apply wp_slice_append $$ [Hout Hcap Hrq] as %s3 ⟨Hs3, Hcap3, -⟩
      · iframe
      try wp_auto
      ihave Hacc' : ([∗list] r;s ∈ gsl2 ++ rqs;acc2 ++ tr.requestVoteIfLogged ts (uint.nat y) (uint.nat y2),
          stateRO (GF := GF) r s) $$ [Hacc Hrl]
      · iapply (BigSepL2.bigSepL2_append (Or.inl Hal)).2
        iframe
      wp_for_post
      iframe
      iexists _, _, _, acc2 ++ tr.requestVoteIfLogged ts (uint.nat y) (uint.nat y2), gsl2 ++ rqs
      iframe
      ipureintro
      refine ⟨by clear hacc2; word, by clear hacc2; word, ?_⟩
      rw [hm1', List.take_add_one, hyT2, ← hacc2]; simp
    · try wp_auto
      have hmx : sint.nat m = tr.server.length := by clear hacc2; rw [← Hxll, Hxl.1]; word
      rw [hmx, List.take_length] at hacc2
      wp_for_post
      iframe
      iexists _, _, _, acc2, gsl2
      iframe
      ipureintro
      refine ⟨by clear hacc hacc2; word, by clear hacc hacc2; word, ?_⟩
      rw [hn1', List.take_add_one, hyT, ← hacc2, ← hacc]; simp
  · try wp_auto
    have hnx : sint.nat n = tr.server.length := by clear hacc; rw [← Hxll, Hxl.1]; word
    rw [hnx, List.take_length, ← hout0] at hacc
    subst hacc
    nr_tail))

set_option maxHeartbeats 2000000 in
theorem Trace.nonReceive.wp_proof
    (wp_logline : Trace.logline.spec (GF := GF) (hG := hG))
    (wp_skip : Trace.skipUnusedLogline.spec (GF := GF) (hG := hG))
    (wp_requestVote : Trace.requestVoteIfLogged.spec (GF := GF) (hG := hG))
    (wp_becomeLeader : Trace.becomeLeaderIfLogged.spec (GF := GF) (hG := hG))
    (wp_clientRequest : Trace.clientRequestIfLogged.spec (GF := GF) (hG := hG))
    (wp_advanceCommitIndex : Trace.advanceCommitIndexIfLogged.spec (GF := GF) (hG := hG))
    (wp_appendEntries : Trace.appendEntriesIfLogged.spec (GF := GF) (hG := hG))
    (wp_heartbeat : Trace.heartbeatIfLogged.spec (GF := GF) (hG := hG))
    (wp_appendEntriesToSelf : Trace.appendEntriesToSelfIfLogged.spec (GF := GF) (hG := hG))
    (wp_timeout : Trace.timeoutIfLogged.spec (GF := GF) (hG := hG))
    (wp_preTimeout : Trace.preTimeoutIfLogged.spec (GF := GF) (hG := hG))
    (wp_ignoreInLease : Trace.ignoreInLeaseIfLogged.spec (GF := GF) (hG := hG))
    (wp_applySimpleConfChange : Trace.applySimpleConfChangeIfLogged.spec (GF := GF) (hG := hG))
    (wp_ready : Trace.readyIfLogged.spec (GF := GF) (hG := hG))
    (wp_stepDown : Trace.stepDownToFollowerIfLogged.spec (GF := GF) (hG := hG)) :
    Trace.nonReceive.spec (GF := GF) (hG := hG) := by
  intro t tr g ts sts
  wp_start as ⟨#Ht, #Hts, %Hl1, %Hl2, %Hsv, %Hact, %Hsc, %Hnr⟩
  open_ts
  open_trace
  wp_auto
  wp_apply wp_logline t tr g ts $$ [Ht Hts] as %ql #Hlp
  · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hl2⟩
  open_lineP
  wp_auto
  ihave #Hsrv0 := Hsrv
  iunfold setRO at Hsrv0
  icases Hsrv0 with ⟨%xs, #Hxs, %Hxsm⟩
  ihave %Hxl := ownSlice_len $$ Hxs
  have Hxll : xs.length = tr.server.length := by rw [← Hxsm, List.length_map]
  rw [decide_strRel Hef.1 (show strRel go!"SendRequestVoteResponse" "SendRequestVoteResponse" by strRel_lit)]
  have hrvL : ((tr.line ts.l).ev.name = "SendRequestVoteResponse" ∨
      (tr.line ts.l).ev.name = "SendRequestVoteRequest") → ∃ out0,
      sts = (if tr.skipUnusedLogline ts then out0 ++ [ts.s] else out0) ∧
      out0 = tr.server.flatMap (fun i => tr.server.flatMap (fun j => tr.requestVoteIfLogged ts i j)) := by
    intro hn
    rw [← Trace.pairs_flatMap (f := fun p => tr.requestVoteIfLogged ts p.1 p.2)]
    rcases hn with hn | hn <;>
    · simp [Trace.nonReceive, hn, Bind.bind, Except.bind, Pure.pure, Except.pure] at Hnr
      exact ⟨_, Hnr.symm, rfl⟩
  by_cases n1 : (tr.line ts.l).ev.name = "SendRequestVoteResponse"
  · rw [decide_eq_true n1]
    obtain ⟨out0, hsts, hout0⟩ := hrvL (.inl n1)
    rv_body
  rw [decide_eq_false n1]
  wp_auto
  rw [decide_strRel Hef.1 (show strRel go!"SendRequestVoteRequest" "SendRequestVoteRequest" by strRel_lit)]
  by_cases n2 : (tr.line ts.l).ev.name = "SendRequestVoteRequest"
  · rw [decide_eq_true n2]
    obtain ⟨out0, hsts, hout0⟩ := hrvL (.inr n2)
    rv_body
  rw [decide_eq_false n2]
  wp_auto
  nr_case1 n3, go!"BecomeLeader", "BecomeLeader", (tr.becomeLeaderIfLogged ts) with
    wp_apply wp_becomeLeader t tr g ts y $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hyS, (Hact.2.2.2.2.2 _ hyS).2.1⟩
  nr_case1 n4, go!"Replicate", "Replicate", (fun i => tr.clientRequestIfLogged ts i 0) with
    wp_apply wp_clientRequest t tr g ts y (W64 0) $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hyS⟩
  nr_case1 n5, go!"Commit", "Commit", (tr.advanceCommitIndexIfLogged ts) with
    wp_apply wp_advanceCommitIndex t tr g ts y $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro
      have h := Hact.2.2.2.2.2 _ hyS
      exact ⟨Hl1, hyS, h.2.2.2.1, by omega⟩
  rw [decide_strRel Hef.1 (show strRel go!"SendAppendEntriesRequest" "SendAppendEntriesRequest" by strRel_lit)]
  by_cases n6 : (tr.line ts.l).ev.name = "SendAppendEntriesRequest"
  · rw [decide_eq_true n6]
    have Hnr' := Hnr
    simp only [Trace.nonReceive, n6] at Hnr'
    wp_auto
    cases hmsg : (tr.line ts.l).ev.msg with
    | none =>
      icases Hemsg with %Hmn
      rw [Hmn]
      simp only [hmsg, Option.map_none] at Hnr'
      obtain ⟨out0, hfold, hsts⟩ := except_bind_pure_ok _ _ _ Hnr'
      cases hfold
      wp_auto
      obtain ⟨gsl, hgsl⟩ : ∃ gsl : List Loc, gsl = [] := ⟨_, rfl⟩
      ihave Hout : (zero_val GoSlice : GoSlice) ↦* gsl $$ []
      · rw [hgsl]; iapply ownSlice_nil
      ihave Hcap : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
      · iapply ownSliceCap_nil
      ihave Hacc : ([∗list] r;s ∈ gsl;([] : List State), stateRO (GF := GF) r s) $$ []
      · rw [hgsl]; iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
      nr_tail
    | some ev =>
    icases Hemsg with ⟨%gm, #Hgm, %Hem⟩
    ihave %Hgmnn := typedPointsto_not_null $$ Hgm
    rw [decide_eq_false Hgmnn]
    wp_auto
    icases typedPointsto_split _ _ _ $$ Hgm with Hgmf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hgmf
    simp only [hmsg, Option.map_some] at Hnr'
    wp_auto
    rw [decide_strRel Hem.1 (show strRel go!"MsgApp" "MsgApp" by strRel_lit)]
    by_cases t1 : ev.type = "MsgApp"
    · rw [decide_eq_true t1]
      simp only [t1] at Hnr'
      obtain ⟨out0, hfold, hsts⟩ := except_bind_pure_ok _ _ _ Hnr'
      rw [Trace.pairs_foldlM] at hfold
      obtain ⟨F1, hF1, hF1d⟩ : ∃ F1 : List State → ID → EvalM (List State), tr.server.foldlM F1 [] = .ok out0 ∧
          ∀ acc i, F1 acc i = tr.server.foldlM (fun (acc : List State) j =>
            (intRange ((ts.s.s i).matchIndex j + 1) (((ts.s.s i).log.length : Int) + 1)).foldlM (fun acc b =>
              (intRange ((ts.s.s i).matchIndex j + 1) (((ts.s.s i).log.length : Int) + 1)).foldlM (fun acc e => do
                let r ← tr.appendEntriesIfLogged ts i j b e
                return acc ++ r) acc) acc) acc := ⟨_, hfold, fun _ _ => rfl⟩
      clear hfold
      ihave #HstS := Hst
      iunfold stateRO at HstS
      icases HstS with ⟨%gS, %smS, #HpS, -, #HmS, %HkeysS, -, #HsrvsS, -, -, -⟩
      icases typedPointsto_split _ _ _ $$ HpS with HpSf
      simp only [TypedPointsto.typedPointstoDef]
      icases HpSf with ⟨-, #PS2, -⟩
      wp_auto
      rename_i iv_ptr
      irename : (iv_ptr ↦ (zero_val w64 : w64)) => iv
      ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
      · iapply ownSlice_nil
      ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
      · iapply ownSliceCap_nil
      ihave IH : iprop(∃ (n x : w64) (osl : GoSlice) (acc : List State) (gsl : List Loc),
          "iv" ∷ iv_ptr ↦ x ∗ "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ osl ∗
          "Hout" ∷ osl ↦* gsl ∗ "Hcap" ∷ ownSliceCap Loc osl (DFrac.own 1) ∗
          "Hacc" ∷ ([∗list] r;s ∈ gsl;acc, stateRO (GF := GF) r s) ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gt.Server'.len ∧
            (tr.server.take (sint.nat n)).foldlM F1 [] = .ok acc⌝) $$ [iv i out Hnil Hcap0]
      · iexists _, _, _, [], _
        iframe
        isplitr
        · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
        ipureintro
        refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
      wp_for IH
      obtain ⟨hn0, hn1, hacc⟩ := Hn
      wp_if_destruct
      · have Hlt : sint.nat n < xs.length := by clear hacc; rw [Hxl.1]; word
        obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
        have hyS : uint.nat y ∈ ts.s.server := by
          rw [Hsv, ← Hxsm]; exact List.mem_map.2 ⟨y, List.mem_of_getElem? Hy, rfl⟩
        have hyT : tr.server[sint.nat n]? = some (uint.nat y) := by rw [← Hxsm, List.getElem?_map, Hy]; rfl
        have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hacc; word
        obtain ⟨a', hstep, htake'⟩ := foldlM_ok_step _ _ _ _ _ _ _ hF1 hacc hyT
        rw [hF1d] at hstep
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gt.Server'.len from ⟨hn0, Hif⟩))]
        wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
        · isplitr
          · iexact Hxs
          ipureintro; exact Hy
        try wp_auto
        have hyB := Hact.2.2.2.2.2 _ hyS
        icases servers_at ts.s smS y hyS $$ HsrvsS with ⟨%qv, %Hqv, #Hsvr⟩
        iunfold serverRO at Hsvr
        icases Hsvr with ⟨%gv, %mv, #Hqv', %Hfv, #Hlogv, -, -, #Hmmv, %Hmiv, -, -⟩
        icases typedPointsto_split _ _ _ $$ Hqv' with Hqvf
        simp only [TypedPointsto.typedPointstoDef]
        icases Hqvf with ⟨-, -, -, -, #VLog, -, -, -, #VMI, -⟩
        iunfold logRO at Hlogv
        icases Hlogv with ⟨%esv, #Hesv, #Helv⟩
        ihave %Hesvl := ownSlice_len $$ Hesv
        ihave %Hellv := BigSepL2.bigSepL2_length $$ Helv
        ihave IH2 : iprop(∃ (m jv : w64) (osl2 : GoSlice) (acc2 : List State) (gsl2 : List Loc),
            "j" ∷ j_ptr ↦ jv ∗ "i" ∷ i_ptr ↦ m ∗ "out" ∷ out_ptr ↦ osl2 ∗
            "Hout" ∷ osl2 ↦* gsl2 ∗ "Hcap" ∷ ownSliceCap Loc osl2 (DFrac.own 1) ∗
            "Hacc" ∷ ([∗list] r;s ∈ gsl2;acc2, stateRO (GF := GF) r s) ∗
            "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z gt.Server'.len ∧
              (tr.server.take (sint.nat m)).foldlM (fun (acc : List State) j =>
                (intRange ((ts.s.s (uint.nat y)).matchIndex j + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1)).foldlM
                  (fun acc b =>
                  (intRange ((ts.s.s (uint.nat y)).matchIndex j + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1)).foldlM
                    (fun acc e => do
                      let r ← tr.appendEntriesIfLogged ts (uint.nat y) j b e
                      return acc ++ r) acc) acc) acc = .ok acc2⌝)
            $$ [j i out Hout Hcap Hacc]
        · iexists _, _, _, acc, gsl
          iframe
          ipureintro
          refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
        wp_for IH2
        obtain ⟨hm0, hm1, hacc2⟩ := Hm
        wp_if_destruct
        · have Hlt2 : sint.nat m < xs.length := by clear hacc2; rw [Hxl.1]; word
          obtain ⟨y2, Hy2⟩ : ∃ y2, xs[sint.nat m]? = some y2 := ⟨_, List.getElem?_eq_getElem Hlt2⟩
          have hyT2 : tr.server[sint.nat m]? = some (uint.nat y2) := by rw [← Hxsm, List.getElem?_map, Hy2]; rfl
          have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hacc2; word
          obtain ⟨a2, hstep2, htake2⟩ := foldlM_ok_step _ _ _ _ _ _ _ hstep hacc2 hyT2
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z gt.Server'.len from ⟨hm0, Hif⟩))]
          wp_apply wp_load_slice_index _ (sint.Z m) xs DFrac.discard y2 hm0 $$ [Hxs] as -
          · isplitr
            · iexact Hxs
            ipureintro; exact Hy2
          try wp_auto
          wp_apply wp_map_lookup1 $$ [HmS] as -
          · iexact HmS
          rw [Hqv]
          simp only [Option.getD_some]
          try wp_auto
          wp_apply wp_map_lookup1 $$ [Hmmv] as -
          · iexact Hmmv
          try wp_auto
          wp_apply wp_map_lookup1 $$ [HmS] as -
          · iexact HmS
          rw [Hqv]
          simp only [Option.getD_some]
          try wp_auto
          have hmiB := hyB.2.2.2.2 (uint.nat y2)
          have hlo : sint.Z ((mv !! y2).getD (W64 0) + W64 1) = ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) := by
            have := Hmiv y2; rw [← this] at hmiB ⊢; word
          have hlen : sint.Z gv.Log'.len = ((ts.s.s (uint.nat y)).log.length : Int) := by
            rw [← Hellv, Hesvl.1]; word
          have hhi : sint.Z (gv.Log'.len + W64 1) = (((ts.s.s (uint.nat y)).log.length : Int) + 1) := by
            have h1 : ((ts.s.s (uint.nat y)).log.length : Int) + 1 < 2 ^ 62 := by have := hyB.1; omega
            rw [← hlen] at h1 ⊢; word
          obtain ⟨lov, hlov⟩ : ∃ v, v = (mv !! y2).getD (W64 0) + W64 1 := ⟨_, rfl⟩
          obtain ⟨hiv, hhiv⟩ : ∃ v, v = gv.Log'.len + W64 1 := ⟨_, rfl⟩
          rw [show (zero_val w64 : w64) = W64 0 from rfl, ← hlov, ← hhiv]
          rw [← hlov] at hlo
          rw [← hhiv] at hhi
          have hLO : 1 ≤ ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) ∧ ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) < 2 ^ 62 := by constructor <;> omega
          have hHI : 1 ≤ (((ts.s.s (uint.nat y)).log.length : Int) + 1) ∧ (((ts.s.s (uint.nat y)).log.length : Int) + 1) < 2 ^ 62 := by constructor <;> omega
          ihave IH3 : iprop(∃ (bv : w64) (osl3 : GoSlice) (acc3 : List State) (gsl3 : List Loc),
              "b" ∷ b_ptr ↦ bv ∗ "out" ∷ out_ptr ↦ osl3 ∗
              "Hout" ∷ osl3 ↦* gsl3 ∗ "Hcap" ∷ ownSliceCap Loc osl3 (DFrac.own 1) ∗
              "Hacc" ∷ ([∗list] r;s ∈ gsl3;acc3, stateRO (GF := GF) r s) ∗
              "%Hb" ∷ ⌜((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) ≤ sint.Z bv ∧ sint.Z bv ≤ max (((ts.s.s (uint.nat y)).log.length : Int) + 1) (((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) - 1) + 1 ∧
                ((intRange ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1)).take (sint.Z bv - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat).foldlM (fun acc b =>
                  (intRange ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1)).foldlM (fun acc e => do
                    let r ← tr.appendEntriesIfLogged ts (uint.nat y) (uint.nat y2) b e
                    return acc ++ r) acc) acc2 = .ok acc3⌝)
              $$ [b out Hout Hcap Hacc]
          · iexists _, _, acc2, gsl2
            iframe
            ipureintro
            refine ⟨by omega, by omega, by rw [hlo, Int.sub_self]; rfl⟩
          wp_for IH3
          obtain ⟨hb0, hb1, hacc3⟩ := Hb
          wp_if_destruct
          · rw [hhi] at Hif
            have hk : (sint.Z bv - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat < ((((ts.s.s (uint.nat y)).log.length : Int) + 1) - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) + 1).toNat := by omega
            have hxb : (intRange ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1))[(sint.Z bv - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat]? = some (sint.Z bv) := by
              rw [intRange_getElem? _ _ _ hk]; congr 1; omega
            obtain ⟨a3, hstep3, htake3⟩ := foldlM_ok_step _ _ _ _ _ _ _ hstep2 hacc3 hxb
            try wp_auto
            ihave IH4 : iprop(∃ (ev : w64) (osl4 : GoSlice) (acc4 : List State) (gsl4 : List Loc),
                "e" ∷ e_ptr ↦ ev ∗ "out" ∷ out_ptr ↦ osl4 ∗
                "Hout" ∷ osl4 ↦* gsl4 ∗ "Hcap" ∷ ownSliceCap Loc osl4 (DFrac.own 1) ∗
                "Hacc" ∷ ([∗list] r;s ∈ gsl4;acc4, stateRO (GF := GF) r s) ∗
                "%He" ∷ ⌜((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) ≤ sint.Z ev ∧ sint.Z ev ≤ max (((ts.s.s (uint.nat y)).log.length : Int) + 1) (((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) - 1) + 1 ∧
                  ((intRange ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1)).take (sint.Z ev - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat).foldlM (fun acc e => do
                    let r ← tr.appendEntriesIfLogged ts (uint.nat y) (uint.nat y2) (sint.Z bv) e
                    return acc ++ r) acc3 = .ok acc4⌝)
                $$ [e out Hout Hcap Hacc]
            · iexists _, _, acc3, gsl3
              iframe
              ipureintro
              refine ⟨by omega, by omega, by rw [hlo, Int.sub_self]; rfl⟩
            wp_for IH4
            obtain ⟨he0, he1, hacc4⟩ := He
            wp_if_destruct
            · rw [hhi] at Hif
              have hk4 : (sint.Z ev - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat < ((((ts.s.s (uint.nat y)).log.length : Int) + 1) - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) + 1).toNat := by omega
              have hxe : (intRange ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1))[(sint.Z ev - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat]? = some (sint.Z ev) := by
                rw [intRange_getElem? _ _ _ hk4]; congr 1; omega
              obtain ⟨a4, hstep4, htake4⟩ := foldlM_ok_step _ _ _ _ _ _ _ hstep3 hacc4 hxe
              obtain ⟨r, hr, ha4⟩ := except_bind_pure_ok _ _ _ hstep4
              try wp_auto
              wp_apply wp_appendEntries t tr g ts y y2 bv ev r $$ [Ht Hts] as %rsl Hr
              · iframe Ht Hts; ipureintro
                exact ⟨Hl1, hyS, Hact.2.2.1, by omega, by omega, by omega, by omega, hr⟩
              iunfold statesOut at Hr
              icases Hr with ⟨%rqs, Hrq, -, Hrl⟩
              ihave %Hal := BigSepL2.bigSepL2_length $$ Hacc
              wp_apply wp_slice_append $$ [Hout Hcap Hrq] as %s3 ⟨Hs3, Hcap3, -⟩
              · iframe
              try wp_auto
              ihave Hacc' : ([∗list] r;s ∈ gsl4 ++ rqs;acc4 ++ r, stateRO (GF := GF) r s) $$ [Hacc Hrl]
              · iapply (BigSepL2.bigSepL2_append (Or.inl Hal)).2
                iframe
              wp_for_post
              iframe
              iexists _, _, acc4 ++ r, gsl4 ++ rqs
              iframe
              ipureintro
              have hev1 : sint.Z (ev + W64 1) = sint.Z ev + 1 := by word
              refine ⟨by omega, by omega, ?_⟩
              rw [hev1, show (sint.Z ev + 1 - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat = (sint.Z ev - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat + 1 by omega, htake4, ha4]
            · try wp_auto
              rw [hhi] at Hif
              have hfull : (sint.Z ev - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat = (intRange ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1)).length := by
                rw [intRange_length]; omega
              rw [hfull, List.take_length, hstep3] at hacc4
              cases hacc4
              wp_for_post
              iframe
              iexists _, _, a3, gsl4
              iframe
              ipureintro
              have hbv1 : sint.Z (bv + W64 1) = sint.Z bv + 1 := by word
              refine ⟨by omega, by omega, ?_⟩
              rw [hbv1, show (sint.Z bv + 1 - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat = (sint.Z bv - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat + 1 by omega, htake3]
          · try wp_auto
            rw [hhi] at Hif
            have hfull : (sint.Z bv - ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1)).toNat = (intRange ((ts.s.s (uint.nat y)).matchIndex (uint.nat y2) + 1) (((ts.s.s (uint.nat y)).log.length : Int) + 1)).length := by
              rw [intRange_length]; omega
            rw [hfull, List.take_length, hstep2] at hacc3
            cases hacc3
            wp_for_post
            iframe
            iexists _, _, _, a2, gsl3
            iframe
            ipureintro
            refine ⟨by clear hacc2; word, by clear hacc2; word, ?_⟩
            rw [hm1', htake2]
        · try wp_auto
          have hmx : sint.nat m = tr.server.length := by clear hacc2; rw [← Hxll, Hxl.1]; word
          rw [hmx, List.take_length, hstep] at hacc2
          cases hacc2
          wp_for_post
          iframe
          iexists _, _, _, a', gsl2
          iframe
          ipureintro
          refine ⟨by clear hacc; word, by clear hacc; word, ?_⟩
          rw [hn1', htake']
      · try wp_auto
        have hnx : sint.nat n = tr.server.length := by clear hacc; rw [← Hxll, Hxl.1]; word
        rw [hnx, List.take_length, hF1] at hacc
        cases hacc
        nr_tail
    rw [decide_eq_false t1]
    wp_auto
    rw [decide_strRel Hem.1 (show strRel go!"MsgHeartbeat" "MsgHeartbeat" by strRel_lit)]
    by_cases t2 : ev.type = "MsgHeartbeat"
    · rw [decide_eq_true t2]
      simp only [t2] at Hnr'
      obtain ⟨out0, hfold, hsts⟩ := except_bind_pure_ok _ _ _ Hnr'
      rw [Trace.pairs_foldlM] at hfold
      obtain ⟨F1, hF1, hF1d⟩ : ∃ F1 : List State → ID → EvalM (List State), tr.server.foldlM F1 [] = .ok out0 ∧
          ∀ acc i, F1 acc i = tr.server.foldlM (fun (acc : List State) j => do
            let r ← tr.heartbeatIfLogged ts i j
            return acc ++ r) acc := ⟨_, hfold, fun _ _ => rfl⟩
      clear hfold
      wp_auto
      rename_i iv_ptr
      irename : (iv_ptr ↦ (zero_val w64 : w64)) => iv
      ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
      · iapply ownSlice_nil
      ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
      · iapply ownSliceCap_nil
      ihave IH : iprop(∃ (n x : w64) (osl : GoSlice) (acc : List State) (gsl : List Loc),
          "iv" ∷ iv_ptr ↦ x ∗ "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ osl ∗
          "Hout" ∷ osl ↦* gsl ∗ "Hcap" ∷ ownSliceCap Loc osl (DFrac.own 1) ∗
          "Hacc" ∷ ([∗list] r;s ∈ gsl;acc, stateRO (GF := GF) r s) ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gt.Server'.len ∧
            (tr.server.take (sint.nat n)).foldlM F1 [] = .ok acc⌝) $$ [iv i out Hnil Hcap0]
      · iexists _, _, _, [], _
        iframe
        isplitr
        · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
        ipureintro
        refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
      wp_for IH
      obtain ⟨hn0, hn1, hacc⟩ := Hn
      wp_if_destruct
      · have Hlt : sint.nat n < xs.length := by clear hacc; rw [Hxl.1]; word
        obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
        have hyS : uint.nat y ∈ ts.s.server := by
          rw [Hsv, ← Hxsm]; exact List.mem_map.2 ⟨y, List.mem_of_getElem? Hy, rfl⟩
        have hyT : tr.server[sint.nat n]? = some (uint.nat y) := by rw [← Hxsm, List.getElem?_map, Hy]; rfl
        have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hacc; word
        obtain ⟨a', hstep, htake'⟩ := foldlM_ok_step _ _ _ _ _ _ _ hF1 hacc hyT
        rw [hF1d] at hstep
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gt.Server'.len from ⟨hn0, Hif⟩))]
        wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
        · isplitr
          · iexact Hxs
          ipureintro; exact Hy
        try wp_auto
        ihave IH2 : iprop(∃ (m jv : w64) (osl2 : GoSlice) (acc2 : List State) (gsl2 : List Loc),
            "j" ∷ j_ptr ↦ jv ∗ "i" ∷ i_ptr ↦ m ∗ "out" ∷ out_ptr ↦ osl2 ∗
            "Hout" ∷ osl2 ↦* gsl2 ∗ "Hcap" ∷ ownSliceCap Loc osl2 (DFrac.own 1) ∗
            "Hacc" ∷ ([∗list] r;s ∈ gsl2;acc2, stateRO (GF := GF) r s) ∗
            "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z gt.Server'.len ∧
              (tr.server.take (sint.nat m)).foldlM (fun (acc : List State) j => do
                let r ← tr.heartbeatIfLogged ts (uint.nat y) j
                return acc ++ r) acc = .ok acc2⌝)
            $$ [j i out Hout Hcap Hacc]
        · iexists _, _, _, acc, gsl
          iframe
          ipureintro
          refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
        wp_for IH2
        obtain ⟨hm0, hm1, hacc2⟩ := Hm
        wp_if_destruct
        · have Hlt2 : sint.nat m < xs.length := by clear hacc2; rw [Hxl.1]; word
          obtain ⟨y2, Hy2⟩ : ∃ y2, xs[sint.nat m]? = some y2 := ⟨_, List.getElem?_eq_getElem Hlt2⟩
          have hyT2 : tr.server[sint.nat m]? = some (uint.nat y2) := by rw [← Hxsm, List.getElem?_map, Hy2]; rfl
          have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hacc2; word
          obtain ⟨a2, hstep2, htake2⟩ := foldlM_ok_step _ _ _ _ _ _ _ hstep hacc2 hyT2
          obtain ⟨r, hr, ha2⟩ := except_bind_pure_ok _ _ _ hstep2
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z gt.Server'.len from ⟨hm0, Hif⟩))]
          wp_apply wp_load_slice_index _ (sint.Z m) xs DFrac.discard y2 hm0 $$ [Hxs] as -
          · isplitr
            · iexact Hxs
            ipureintro; exact Hy2
          try wp_auto
          wp_apply wp_heartbeat t tr g ts y y2 r $$ [Ht Hts] as %rsl Hr
          · iframe Ht Hts; ipureintro; exact ⟨Hl1, hyS, Hact.2.2.1, hr⟩
          iunfold statesOut at Hr
          icases Hr with ⟨%rqs, Hrq, -, Hrl⟩
          ihave %Hal := BigSepL2.bigSepL2_length $$ Hacc
          wp_apply wp_slice_append $$ [Hout Hcap Hrq] as %s3 ⟨Hs3, Hcap3, -⟩
          · iframe
          try wp_auto
          ihave Hacc' : ([∗list] r;s ∈ gsl2 ++ rqs;acc2 ++ r, stateRO (GF := GF) r s) $$ [Hacc Hrl]
          · iapply (BigSepL2.bigSepL2_append (Or.inl Hal)).2
            iframe
          wp_for_post
          iframe
          iexists _, _, _, acc2 ++ r, gsl2 ++ rqs
          iframe
          ipureintro
          refine ⟨by clear hacc2; word, by clear hacc2; word, ?_⟩
          rw [hm1', htake2, ha2]
        · try wp_auto
          have hmx : sint.nat m = tr.server.length := by clear hacc2; rw [← Hxll, Hxl.1]; word
          rw [hmx, List.take_length, hstep] at hacc2
          cases hacc2
          wp_for_post
          iframe
          iexists _, _, _, a', gsl2
          iframe
          ipureintro
          refine ⟨by clear hacc; word, by clear hacc; word, ?_⟩
          rw [hn1', htake']
      · try wp_auto
        have hnx : sint.nat n = tr.server.length := by clear hacc; rw [← Hxll, Hxl.1]; word
        rw [hnx, List.take_length, hF1] at hacc
        cases hacc
        nr_tail
    rw [decide_eq_false t2]
    wp_auto
    have t3 : ev.type ≠ "MsgSnap" := by
      have := Hsc.2.2 n6; rw [hmsg] at this; simpa using this
    rw [decide_strRel Hem.1 (show strRel go!"MsgSnap" "MsgSnap" by strRel_lit), decide_eq_false t3]
    wp_auto
    split at Hnr'
    · rename_i heq; exact absurd (Option.some.inj heq) t1
    · rename_i heq; exact absurd (Option.some.inj heq) t2
    · rename_i heq; exact absurd (Option.some.inj heq) t3
    obtain ⟨out0, hfold, hsts⟩ := except_bind_pure_ok _ _ _ Hnr'
    cases hfold
    obtain ⟨gsl, hgsl⟩ : ∃ gsl : List Loc, gsl = [] := ⟨_, rfl⟩
    ihave Hout : (zero_val GoSlice : GoSlice) ↦* gsl $$ []
    · rw [hgsl]; iapply ownSlice_nil
    ihave Hcap : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    ihave Hacc : ([∗list] r;s ∈ gsl;([] : List State), stateRO (GF := GF) r s) $$ []
    · rw [hgsl]; iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    nr_tail
  rw [decide_eq_false n6]
  wp_auto
  nr_case1 n7, go!"SendAppendEntriesResponse", "SendAppendEntriesResponse", (tr.appendEntriesToSelfIfLogged ts) with
    wp_apply wp_appendEntriesToSelf t tr g ts y $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hyS, Hact.2.2.1⟩
  nr_case1 n8, go!"BecomeCandidate", "BecomeCandidate", (tr.timeoutIfLogged ts) with
    wp_apply wp_timeout t tr g ts y $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro
      have h := Hact.2.2.2.2.2 _ hyS
      exact ⟨Hl1, hyS, h.2.2.1, h.2.1⟩
  nr_case1 n9, go!"BecomePreCandidate", "BecomePreCandidate", (tr.preTimeoutIfLogged ts) with
    wp_apply wp_preTimeout t tr g ts y $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hyS, Hact.1⟩
  rw [decide_strRel Hef.1 (show strRel go!"IgnoreRequestVoteRequest" "IgnoreRequestVoteRequest" by strRel_lit)]
  by_cases n10 : (tr.line ts.l).ev.name = "IgnoreRequestVoteRequest"
  · rw [decide_eq_true n10]
    obtain ⟨out0, hsts, hout0⟩ : ∃ out0, sts = (if tr.skipUnusedLogline ts then out0 ++ [ts.s] else out0) ∧
        out0 = tr.ignoreInLeaseIfLogged ts := by
      simp [Trace.nonReceive, n10, Bind.bind, Except.bind, Pure.pure, Except.pure] at Hnr
      exact ⟨_, Hnr.symm, rfl⟩
    subst hout0
    wp_auto
    wp_apply wp_ignoreInLease t tr g ts $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, Hact.2.1⟩
    iunfold statesOut at Hr
    icases Hr with ⟨%rqs, Hrq, -, Hrl⟩
    ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
    · iapply ownSlice_nil
    ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    wp_apply wp_slice_append $$ [Hnil Hcap0 Hrq] as %s3 ⟨Hout, Hcap, -⟩
    · iframe
    try wp_auto
    obtain ⟨gsl, hgsl⟩ : ∃ gsl : List Loc, gsl = [] ++ rqs := ⟨_, rfl⟩
    rw [← hgsl]
    ihave Hacc : ([∗list] r;s ∈ gsl;tr.ignoreInLeaseIfLogged ts, stateRO (GF := GF) r s) $$ [Hrl]
    · rw [hgsl, List.nil_append]; iexact Hrl
    nr_tail
  rw [decide_eq_false n10]
  wp_auto
  rw [decide_strRel Hef.1 (show strRel go!"ChangeConf" "ChangeConf" by strRel_lit), decide_eq_false Hsc.1]
  wp_auto
  rw [decide_strRel Hef.1 (show strRel go!"ApplyConfChange" "ApplyConfChange" by strRel_lit)]
  by_cases n12 : (tr.line ts.l).ev.name = "ApplyConfChange"
  · rw [decide_eq_true n12]
    have Hnr' := Hnr
    simp only [Trace.nonReceive, n12] at Hnr'
    obtain ⟨out0, hfold, hsts⟩ := except_bind_pure_ok _ _ _ Hnr'
    wp_auto
    rename_i iv_ptr
    irename : (iv_ptr ↦ (zero_val w64 : w64)) => iv
    ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List Loc) $$ []
    · iapply ownSlice_nil
    ihave Hcap0 : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    ihave IH : iprop(∃ (n x : w64) (osl : GoSlice) (acc : List State) (gsl : List Loc),
        "iv" ∷ iv_ptr ↦ x ∗ "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ osl ∗
        "Hout" ∷ osl ↦* gsl ∗ "Hcap" ∷ ownSliceCap Loc osl (DFrac.own 1) ∗
        "Hacc" ∷ ([∗list] r;s ∈ gsl;acc, stateRO (GF := GF) r s) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z gt.Server'.len ∧
          (tr.server.take (sint.nat n)).foldlM (fun (acc : List State) i => do
            let __do_lift ← tr.applySimpleConfChangeIfLogged ts i
            Pure.pure (acc ++ __do_lift)) [] = .ok acc⌝) $$ [iv i out Hnil Hcap0]
    · iexists _, _, _, [], _
      iframe
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
    wp_for IH
    obtain ⟨hn0, hn1, hacc⟩ := Hn
    wp_if_destruct
    · have Hlt : sint.nat n < xs.length := by clear hacc; rw [Hxl.1]; word
      obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have hyS : uint.nat y ∈ ts.s.server := by
        rw [Hsv, ← Hxsm]; exact List.mem_map.2 ⟨y, List.mem_of_getElem? Hy, rfl⟩
      have hyT : tr.server[sint.nat n]? = some (uint.nat y) := by rw [← Hxsm, List.getElem?_map, Hy]; rfl
      have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hacc; word
      obtain ⟨a', hstep, htake'⟩ := foldlM_ok_step _ _ _ _ _ _ _ hfold hacc hyT
      obtain ⟨r, hr, ha'⟩ := except_bind_pure_ok _ _ _ hstep
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gt.Server'.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index _ (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
      · isplitr
        · iexact Hxs
        ipureintro; exact Hy
      try wp_auto
      wp_apply wp_applySimpleConfChange t tr g ts y r $$ [Ht Hts] as %rsl Hr
      · iframe Ht Hts; ipureintro
        have h := Hact.2.2.2.2.2 _ hyS
        exact ⟨Hl1, hyS, by omega, Hact.2.2.2.2.1, hr⟩
      iunfold statesOut at Hr
      icases Hr with ⟨%rqs, Hrq, -, Hrl⟩
      ihave %Hal := BigSepL2.bigSepL2_length $$ Hacc
      wp_apply wp_slice_append $$ [Hout Hcap Hrq] as %s3 ⟨Hs3, Hcap3, -⟩
      · iframe
      try wp_auto
      ihave Hacc' : ([∗list] r;s ∈ gsl ++ rqs;acc ++ r, stateRO (GF := GF) r s) $$ [Hacc Hrl]
      · iapply (BigSepL2.bigSepL2_append (Or.inl Hal)).2
        iframe
      wp_for_post
      iframe
      iexists _, _, _, acc ++ r, gsl ++ rqs
      iframe
      ipureintro
      refine ⟨by clear hacc; word, by clear hacc; word, ?_⟩
      rw [hn1', htake', ha']
    · try wp_auto
      have hnx : sint.nat n = tr.server.length := by clear hacc; rw [← Hxll, Hxl.1]; word
      rw [hnx, List.take_length, hfold] at hacc
      cases hacc
      nr_tail
  rw [decide_eq_false n12]
  wp_auto
  nr_case1 n13, go!"Ready", "Ready", (tr.readyIfLogged ts) with
    wp_apply wp_ready t tr g ts y $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hyS, Hact.2.2.1.1, Hact.2.2.2.1⟩
  rw [decide_strRel Hef.1 (show strRel go!"InitState" "InitState" by strRel_lit), decide_eq_false Hsc.2.1]
  wp_auto
  nr_case1 n15, go!"BecomeFollower", "BecomeFollower", (tr.stepDownToFollowerIfLogged ts) with
    wp_apply wp_stepDown t tr g ts y $$ [Ht Hts] as %rsl Hr
    · iframe Ht Hts; ipureintro; exact ⟨Hl1, hyS⟩
  -- no case: no successor from the actions
  obtain ⟨out0, hsts, hout0⟩ : ∃ out0, sts = (if tr.skipUnusedLogline ts then out0 ++ [ts.s] else out0) ∧
      out0 = [] := by
    simp [Trace.nonReceive, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, Hsc.1, n12, n13, Hsc.2.1, n15, Bind.bind,
      Except.bind, Pure.pure, Except.pure] at Hnr
    exact ⟨_, Hnr.symm, rfl⟩
  subst hout0
  obtain ⟨gsl, hgsl⟩ : ∃ gsl : List Loc, gsl = [] := ⟨_, rfl⟩
  ihave Hout : (zero_val GoSlice : GoSlice) ↦* gsl $$ []
  · rw [hgsl]; iapply ownSlice_nil
  ihave Hcap : ownSliceCap Loc (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave Hacc : ([∗list] r;s ∈ gsl;([] : List State), stateRO (GF := GF) r s) $$ []
  · rw [hgsl]; iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
  nr_tail

end proof

end Etcdraft
end EtcdGrove
end Perennial
