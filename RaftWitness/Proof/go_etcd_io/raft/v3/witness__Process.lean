/-
Proof of `Spec/go_etcd_io/raft/v3/witness__Process.lean` (2026-10-20, witness support, W3b).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__Process
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__processNoUpdate
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__cloneState
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__processMessageWithNewerTerm
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__handleHeartbeat
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__handleAppend
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__handleVote
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem respOpt_some (ml : Loc) (r : WResp) :
    respOpt (GF := GF) ml (some r) = msgOwn ml (DFrac.own 1) ⟨r.1, [], none, r.2, []⟩ := rfl

/-- A round's obligation when nothing is written: the answer's `Φr`. -/
theorem wObl_none (id : w64) (cq pv : Bool) (N : Namespace) (P Lb : WHS → IProp GF)
    (Φr : Option WResp → IProp GF) (μ : WMsg) (σ : WHS) (r : Option WResp)
    (h : wStep id cq pv σ μ = (none, r)) :
    wObl id cq pv N P Lb Φr μ σ ⊢ Φr r := by
  unfold wObl; rw [h]

/-- A round's obligation when `σ'` is written: the write's shift. -/
theorem wObl_some (id : w64) (cq pv : Bool) (N : Namespace) (P Lb : WHS → IProp GF)
    (Φr : Option WResp → IProp GF) (μ : WMsg) (σ σ' : WHS) (r : Option WResp)
    (h : wStep id cq pv σ μ = (some σ', r)) :
    wObl id cq pv N P Lb Φr μ σ ⊢ (P σ ={⊤ \ ↑N}=∗ P σ' ∗ Lb σ' ∗ Φr r) := by
  unfold wObl; rw [h]

theorem witness.Process.wp_proof
    (wp_processNoUpdate : witness.processNoUpdate.spec (GF := GF) (hG := hG))
    (wp_cloneState : witness.cloneState.spec (GF := GF) (hG := hG))
    (wp_processMessageWithNewerTerm : witness.processMessageWithNewerTerm.spec (GF := GF) (hG := hG))
    (wp_handleHeartbeat : witness.handleHeartbeat.spec (GF := GF) (hG := hG))
    (wp_handleAppend : witness.handleAppend.spec (GF := GF) (hG := hG))
    (wp_handleVote : witness.handleVote.spec (GF := GF) (hG := hG))
    (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG)) :
    witness.Process.spec (GF := GF) (hG := hG) := by
  intro w id s cq pv c h N P Lb Φr mv μ HLb
  wp_start as ⟨Hw, #Hs, #Hm, #HLbc, #Hcch, #Hread, #Hnone⟩
  iunfold ownWitness at Hw
  iNamed Hw
  ihave #Hm' := Hm
  iunfold ownWMsg at Hm'
  icases Hm' with ⟨%s0, %s1, %Hmv, -, -, -, -⟩
  obtain ⟨Hty, Hfr, Hto, Hte, Hlt, Hls, Hli, Hrs⟩ := Hmv
  wp_auto
  -- the request types the witness answers: heartbeat, pre-vote, vote, append
  wp_bind (If (Val #(decide (mv.Type' = W32 8))) (Val #true) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (mv.Type' = W32 8 ∨ mv.Type' = W32 17 ∨
      mv.Type' = W32 5 ∨ mv.Type' = W32 3))⌝))) $$ []
  · by_cases h8 : mv.Type' = W32 8
    · rw [decide_eq_true h8]; wp_auto; ipureintro; simp [h8]
    rw [decide_eq_false h8]
    wp_auto
    try rw [show raftpb.MsgPreVote = #((W32 17 : raftpb.MessageType)) from rfl]
    by_cases h17 : mv.Type' = W32 17
    · rw [decide_eq_true h17]; wp_auto; ipureintro; simp [h17]
    rw [decide_eq_false h17]
    wp_auto
    try rw [show raftpb.MsgVote = #((W32 5 : raftpb.MessageType)) from rfl]
    by_cases h5 : mv.Type' = W32 5
    · rw [decide_eq_true h5]; wp_auto; ipureintro; simp [h5]
    rw [decide_eq_false h5]
    wp_auto
    try rw [show raftpb.MsgApp = #((W32 3 : raftpb.MessageType)) from rfl]
    ipureintro
    congr 1
    by_cases h3 : mv.Type' = W32 3 <;> simp_all
  iintro %v %Hv
  subst Hv
  by_cases Hsw : mv.Type' = W32 8 ∨ mv.Type' = W32 17 ∨ mv.Type' = W32 5 ∨ mv.Type' = W32 3
  rotate_left
  · -- another type: no answer
    rw [decide_eq_false Hsw]
    wp_auto
    iapply HΦ
    iexists c, h
    iframe HLbc
    isplitl [Hstate HlastError]
    · unfold ownWitness; iexists p, e; iframe Hstate HlastError Hcache Hid Hstorage HpreVote
        HcheckQuorum; ipureintro; exact Hh
    ileft
    isplitr; · ipureintro; rfl
    iexists none
    iframe Hnone
    unfold respOpt; ipureintro; rfl
  rw [decide_eq_true Hsw]
  have Hty4 : μ.ty = MsgHeartbeat ∨ μ.ty = MsgApp ∨ μ.ty = MsgVote ∨ μ.ty = MsgPreVote := by
    rw [← Hty]
    rcases Hsw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  wp_auto
  -- the cache first
  wp_apply wp_processNoUpdate w id cq pv (DFrac.own 1) (DFrac.own 1) p c e mv μ
    $$ [$Hstate $HlastError] as %ml0 %h0 ⟨Hstate, HlastError, Hr0⟩
  · iframe Hid HcheckQuorum HpreVote Hcache Hm
  cases Hc0 : wNoUpdate id cq pv (decide (e = interface.nil)) c μ with
  | some r =>
    icases Hr0 with ⟨%Hh0, Hr⟩
    subst Hh0
    wp_auto
    iapply HΦ
    iexists c, h
    iframe HLbc
    isplitl [Hstate HlastError]
    · unfold ownWitness; iexists p, e; iframe Hstate HlastError Hcache Hid Hstorage HpreVote
        HcheckQuorum; ipureintro; exact Hh
    ileft
    isplitr; · ipureintro; rfl
    iexists r
    iframe Hr
    iapply Hcch $$ HLbc %Hc0
  | none =>
  icases Hr0 with %Hh0
  subst Hh0
  wp_auto
  -- the loop: the cache a state with `Lb`, the last error any
  ihave HI : (∃ (c : WHS) (p : Loc) (e : GoError) (ml : Loc) (hd : Bool),
      "Hstate" ∷ w.[witness, go!"state"] ↦ p ∗ "#Hcache" ∷ whsOpt p c ∗
      "HlastError" ∷ w.[witness, go!"lastError"] ↦ e ∗ "#HLbc" ∷ Lb c ∗
      "resp" ∷ resp_ptr ↦ ml ∗ "handled" ∷ handled_ptr ↦ hd ∗
      "w" ∷ w_ptr ↦ w ∗ "m" ∷ m_ptr ↦ mv : IProp GF)
    $$ [Hstate HlastError resp handled w m]
  · iexists c, p, e, ml0, false
    iframe Hstate Hcache HlastError HLbc resp handled w m
  iclear Hcache HLbc
  wp_for HI
  iNamed Hs
  subst Hs
  wp_auto
  -- the read: the state read, its `Lb`, the round's obligation
  wp_bind (App (Val #(methods i.ty go!"GetWitnessState" i.v)) (Val #()))
  ihave HGet' := HGet $$ %(fun σ => iprop(Lb σ ∗ wObl id cq pv N P Lb Φr μ σ))
  iapply HGet' $$ []
  · iintro %σ HP
    iapply Hread $$ %σ %Hty4 HP
  inext
  iintro %sv %err Hrd
  icases Hrd with (⟨%Herr, -⟩ | ⟨%Herr, %σ, #Hws, #HLbσ, Hobl⟩)
  · -- a storage error: none answered
    wp_auto
    obtain ⟨ie, rfl⟩ : ∃ ie, err = interface.ok ie := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok ie => exact ⟨ie, rfl⟩
    wp_auto
    wp_for_post
    iapply HΦ
    iexists c, false
    iframe HLbc
    isplitl [Hstate HlastError]
    · unfold ownWitness; iexists p, _; iframe Hstate HlastError Hcache Hid Hstorage HpreVote
        HcheckQuorum; ipureintro; simp
    iright
    iframe; ipureintro; exact ⟨nofun, rfl⟩
  subst Herr
  wp_auto
  iclear HGet'
  iunfold isWState at Hws
  iNamed Hws
  subst Hsv
  wp_auto
  wp_bind (App (Val #(methods j.ty go!"GetState" j.v)) (Val #()))
  iapply HGetState $$ []
  · itrivial
  inext
  iintro -
  wp_auto
  -- `m.Type == MsgHeartbeat && m.Term == w.state.GetState().GetTerm()`
  try rw [Hty, show raftpb.MsgHeartbeat = #((W32 8 : raftpb.MessageType)) from rfl]
  wp_bind (If (Val #(decide (μ.ty = W32 8))) _ (Val #false))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (μ.ty = W32 8 ∧ μ.term = σ.term))⌝ ∗
      m_ptr ↦ mv ∗ w_ptr ↦ w ∗ w.[witness, go!"state"] ↦ p))) $$ [m w Hstate]
  · by_cases h8 : μ.ty = W32 8
    · rw [decide_eq_true h8]
      wp_auto
      wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps #Hhs
      wp_apply wp_hsOptW_GetTerm wp_GetTerm ps _ σ $$ [$Hhs] as -
      rw [Hte]
      iframe m w Hstate
      ipureintro
      simp [h8]
    · rw [decide_eq_false h8]
      wp_auto
      iframe m w Hstate
      rw [show decide (μ.ty = W32 8 ∧ μ.term = σ.term) = false from decide_eq_false (fun h => h8 h.1)]
      ipureintro; rfl
  iintro %v ⟨%Hv, m, w, Hstate⟩
  subst Hv
  by_cases Hhb : μ.ty = W32 8 ∧ μ.term = σ.term
  · -- a heartbeat of the stored term: answered without a write
    rw [decide_eq_true Hhb]
    wp_auto
    wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps #Hhs
    wp_apply wp_hsOptW_GetTerm wp_GetTerm ps _ σ $$ [$Hhs] as -
    wp_apply wp_handleHeartbeat w id mv μ σ.term $$ [] as %ml1 Hml1
    · iframe Hid Hm
    have Hws : wStep id cq pv σ μ = (none, some (wHeartbeat id σ.term μ)) := by
      unfold wStep; rw [if_pos (show μ.ty = MsgHeartbeat ∧ μ.term = σ.term from Hhb)]
    ihave HΦr := wObl_none id cq pv N P Lb Φr μ σ _ Hws $$ Hobl
    wp_for_post
    iapply HΦ
    iexists σ, true
    iframe HLbσ
    isplitl [Hstate HlastError]
    · unfold ownWitness; iexists p, _; iframe Hstate HlastError Hp Hid Hstorage HpreVote
        HcheckQuorum; ipureintro; simp
    ileft
    isplitr; · ipureintro; rfl
    iexists (some (wHeartbeat id σ.term μ))
    iframe HΦr
    simp only [respOpt, wHeartbeat]
    iexact Hml1
  rw [decide_eq_false Hhb]
  wp_auto
  -- the state read, as the cache
  wp_apply wp_processNoUpdate w id cq pv (DFrac.own 1) (DFrac.own 1) p σ interface.nil mv μ
    $$ [$Hstate $HlastError] as %ml2 %h2 ⟨Hstate, HlastError, Hr2⟩
  · iframe Hid HcheckQuorum HpreVote Hp Hm
  cases Hc2 : wNoUpdate id cq pv true σ μ with
  | some r =>
    icases Hr2 with ⟨%Hh2, Hr⟩
    subst Hh2
    have Hws : wStep id cq pv σ μ = (none, r) := by
      unfold wStep
      rw [if_neg (show ¬ (μ.ty = MsgHeartbeat ∧ μ.term = σ.term) from Hhb), Hc2]
    ihave HΦr := wObl_none id cq pv N P Lb Φr μ σ _ Hws $$ Hobl
    wp_auto
    wp_for_post
    iapply HΦ
    iexists σ, true
    iframe HLbσ
    isplitl [Hstate HlastError]
    · unfold ownWitness; iexists p, _; iframe Hstate HlastError Hp Hid Hstorage HpreVote
        HcheckQuorum; ipureintro; simp
    ileft
    isplitr; · ipureintro; rfl
    iexists r
    iframe HΦr Hr
  | none =>
  icases Hr2 with %Hh2
  subst Hh2
  wp_auto
  -- the state to write: a copy of the one read, raised to a newer term
  wp_apply wp_cloneState w (DFrac.own 1) p σ $$ [$Hstate $Hp] as %q ⟨Hstate, Hq⟩
  wp_apply wp_whsOwn_GetState wp_GetState q σ $$ [$Hq] as %ps ⟨Hhs, Hqback⟩
  wp_apply wp_hsF_GetTerm wp_GetTerm ps _ σ $$ [$Hhs] as Hhs
  ihave Hq := Hqback $$ Hhs
  rw [Hte]
  wp_join iprop("Hq" ∷ whsOwn q (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) ∗
      "m" ∷ m_ptr ↦ mv ∗ "w" ∷ w_ptr ↦ w ∗ "st" ∷ st_ptr ↦ q) with [Hq m w st]
  · -- a newer term: raised
    wp_apply wp_processMessageWithNewerTerm w mv μ q σ $$ [$Hq] as Hq
    · iframe Hm
    wp_join_done
    rw [if_pos (by simpa using Hif)]
    iframe Hq m w st
  · rw [if_neg (by simpa using Hif)]
    iframe Hq m w st
  iNamed 1
  -- the handler: the state to write and the answer, `wStep`'s
  -- `wStep` past its no-write cases: the copy, raised to a newer term
  have Hwst : ∀ (f : WHS → WMsg → WHS × WResp),
      wStep id cq pv σ μ =
        (let st := if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ
         if μ.ty = MsgHeartbeat then (some st, some (wHeartbeat id st.term μ))
         else if μ.ty = MsgApp then ((some (wAppend id σ st μ).1), some (wAppend id σ st μ).2)
         else (some (wVote id st μ).1, some (wVote id st μ).2)) := by
    intro _
    unfold wStep
    rw [if_neg (show ¬ (μ.ty = MsgHeartbeat ∧ μ.term = σ.term) from Hhb), Hc2]
  have Hwst' := Hwst (fun _ _ => (σ, (respM MsgAppResp 0 0 0 0 false, [])))
  clear Hwst
  wp_auto
  rw [Hty]
  wp_join iprop(∃ (σw : WHS) (rm : MessageM) (rc : List w8) (mlw : Loc),
      "Hq" ∷ whsOwn q σw ∗ "resp" ∷ resp_ptr ↦ mlw ∗
      "Hr" ∷ msgOwn mlw (DFrac.own 1) ⟨rm, [], none, rc, []⟩ ∗
      "%Hws" ∷ ⌜wStep id cq pv σ μ = (some σw, some (rm, rc))⌝ ∗
      "m" ∷ m_ptr ↦ mv ∗ "w" ∷ w_ptr ↦ w ∗ "st" ∷ st_ptr ↦ q ∗
      "Hstate" ∷ w.[witness, go!"state"] ↦ p) with [Hq m w st resp Hstate]
  · -- a heartbeat (of a newer term): answered at the raised term
    wp_apply wp_whsOwn_GetState wp_GetState q _ $$ [$Hq] as %ps' ⟨Hhs, Hqback⟩
    wp_apply wp_hsF_GetTerm wp_GetTerm ps' _ _ $$ [$Hhs] as Hhs
    ihave Hq := Hqback $$ Hhs
    wp_apply wp_handleHeartbeat w id mv μ _ $$ [] as %ml1 Hml1
    · iframe Hid Hm
    isplitr; · ipureintro; rfl
    iexists _, _, _, ml1
    isplitl [Hq]; · iexact Hq
    isplitl [resp]; · iexact resp
    isplitl [Hml1]; · iexact Hml1
    isplitr
    · ipureintro
      rw [Hwst']
      simp only [show μ.ty = MsgHeartbeat from by simpa [MsgHeartbeat] using Hif, ↓reduceIte,
        wHeartbeat]
    iframe m w st Hstate
  · have h8 : ¬ μ.ty = MsgHeartbeat := by simpa [MsgHeartbeat] using Hif
    wp_if_destruct
    · -- an append
      wp_apply wp_handleAppend w id (DFrac.own 1) p σ mv μ q _ $$ [$Hstate $Hq] as %ml1
        ⟨Hstate, Hq, Hml1⟩
      · iframe Hid Hp Hm
      isplitr; · ipureintro; rfl
      iexists _, _, _, ml1
      isplitl [Hq]; · iexact Hq
      isplitl [resp]; · iexact resp
      isplitl [Hml1]; · iexact Hml1
      isplitr
      · ipureintro
        rw [Hwst']
        simp only [show μ.ty = MsgApp from by simpa [MsgApp] using Hif, ↓reduceIte]
        simp [wAppend, MsgApp, MsgHeartbeat]
      iframe m w st Hstate
    · -- a vote or a pre-vote (no other type comes here: `Process` returns at once for one)
      have h3 : ¬ μ.ty = MsgApp := by simpa [MsgApp] using Hif
      have Hvp : μ.ty = W32 5 ∨ μ.ty = W32 17 := by
        rw [Hty] at Hsw
        rcases Hsw with h | h | h | h
        · exact absurd h (by simpa [MsgHeartbeat] using h8)
        · right; exact h
        · left; exact h
        · exact absurd h (by simpa [MsgApp] using h3)
      try rw [show raftpb.MsgPreVote = #((W32 17 : raftpb.MessageType)) from rfl]
      wp_bind (If (Val #(decide (μ.ty = W32 5))) (Val #true) _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #true⌝))) $$ []
      · rcases Hvp with h | h
        · rw [decide_eq_true h]; wp_auto; ipureintro; rfl
        · rw [decide_eq_false (show ¬ μ.ty = W32 5 from by rw [h]; simp)]
          wp_auto
          rw [decide_eq_true h]
          ipureintro; rfl
      iintro %v %Hv
      subst Hv
      wp_auto
      wp_apply wp_handleVote w id mv μ q _ $$ [$Hq] as %ml1 ⟨Hq, Hml1⟩
      · iframe Hid Hm
      isplitr; · ipureintro; rfl
      iexists _, _, _, ml1
      isplitl [Hq]; · iexact Hq
      isplitl [resp]; · iexact resp
      isplitl [Hml1]; · iexact Hml1
      isplitr
      · ipureintro
        rw [Hwst']
        simp only [h8, h3, ↓reduceIte]
        simp [wVote]
      iframe m w st Hstate
  iintro ⟨%σw, %rm, %rc, %mlw, Hj⟩
  iNamed Hj
  -- the write: the compare-and-swap, the obligation's shift at its linearization point
  imod whsOwn_freeze $$ Hq with #Hq
  ihave Hsh := wObl_some id cq pv N P Lb Φr μ σ σw (some (rm, rc)) Hws $$ Hobl
  wp_auto
  wp_bind (App (Val #(methods j.ty go!"Update" j.v)) (Val #q))
  iapply HUpdate $$ %q %σw %(iprop(Lb σw ∗ Φr (some (rm, rc)))) [Hsh]
  · iframe Hq Hsh
  inext
  iintro %err' Hres
  wp_auto
  ihave #Hinit := isInitialized_access $$ Hpkg
  iNamed Hinit
  icases ErrWitnessStateModified with ⟨%ew, #Hew, %Hewf⟩
  obtain ⟨Hewnz, tw, pw, rfl⟩ := Hewf
  icases Hres with (⟨%He, #HLbw, HΦr⟩ | ⟨%He, -⟩)
  · -- written: the cache is the written state, the answer the round's
    subst He
    wp_auto
    wp_for_post
    iapply HΦ
    iexists σw, true
    iframe HLbw
    isplitl [Hstate HlastError]
    · unfold ownWitness; iexists q, _
      iframe Hstate HlastError Hid Hstorage HpreVote HcheckQuorum
      isplitr
      · unfold whsOpt; iright; iexact Hq
      ipureintro; simp
    ileft
    isplitr; · ipureintro; rfl
    iexists (some (rm, rc))
    iframe HΦr
    rw [respOpt_some]
    iexact Hr
  · -- refused: retried on `ErrWitnessStateModified`, else returned
    obtain ⟨Henz, te, pe, rfl⟩ := He
    wp_auto
    -- `err == ErrWitnessStateModified`: retried
    by_cases Hsame : te.PointerType = tw.PointerType ∧ pe = pw
    · obtain ⟨Ht, Hp'⟩ := Hsame
      rw [if_pos Ht]
      subst Hp'
      wp_auto
      wp_for_post
      iframe HΦ
      iexists σ, p, interface.nil, mlw, false
      iframe Hstate Hp HlastError HLbσ resp handled w m
    · -- another error: returned, recorded
      by_cases Ht : te.PointerType = tw.PointerType
      · rw [if_pos Ht]
        have Hne : pe ≠ pw := fun h => Hsame ⟨Ht, h⟩
        wp_auto
        rw [decide_eq_false Hne]
        wp_auto
        wp_for_post
        iapply HΦ
        iexists σ, false
        iframe HLbσ
        isplitl [Hstate HlastError]
        · unfold ownWitness; iexists p, _
          iframe Hstate HlastError Hp Hid Hstorage HpreVote HcheckQuorum
          ipureintro; simp
        iright
        iframe; ipureintro; exact ⟨nofun, rfl⟩
      · rw [if_neg Ht]
        wp_auto
        wp_for_post
        iapply HΦ
        iexists σ, false
        iframe HLbσ
        isplitl [Hstate HlastError]
        · unfold ownWitness; iexists p, _
          iframe Hstate HlastError Hp Hid Hstorage HpreVote HcheckQuorum
          ipureintro; simp
        iright
        iframe; ipureintro; exact ⟨nofun, rfl⟩

end proof

end EtcdGrove
end Perennial
