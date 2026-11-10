/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.InvPbMsg
public import Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__abortLeaderTransfer
public import Proof.go_etcd_io.raft.v3.TracedUntracedRaftStep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type: `MsgBeat` is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [tickMsg_Type', MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

/-- The two counters; past the election timeout the counter is reset, (2026-10-17) with
`checkQuorum` on the quorum check is stepped (`MsgCheckQuorum`: a leader may step down at its
term), and (2026-10-13) a leader's leader transfer is aborted (`abortLeaderTransfer`, which
the protocol does not see: the state after it, `s1`, is `s` with `lt := 0`); then for a
leader past the heartbeat timeout `raft.Step` of a `MsgBeat`. -/
theorem raft.tickHeartbeat.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_raft_abortLeaderTransfer : raft.abortLeaderTransfer.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.tickHeartbeat.spec (GF := GF) (hG := hG) := by
  -- (2026-11-10, Q8 stage 1 slice 12) `Step`'s gated spec, the caller's resources passed through
  intro c md γ r id s R Gm Gout Hwf Hpc
  wp_start as H
  iNamed H
  wp_auto_lc 2
  -- `r.heartbeatElapsed++`, `r.electionElapsed++`
  wp_apply raft.wp_load_heartbeatElapsedC $$ Hphys as %v1 Hphys
  wp_apply raft.wp_store_heartbeatElapsedC $$ Hphys as Hphys
  wp_apply raft.wp_load_electionElapsedC $$ Hphys as %v2 Hphys
  wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
  wp_apply raft.wp_load_electionElapsedC $$ Hphys as %v3 Hphys
  wp_apply raft.wp_load_electionTimeoutC $$ Hphys as %v4 ⟨Hphys, -⟩
  -- the election-timeout block, joined at the state `s2` it leaves: `s1` (the caller's `Gm s1`),
  -- its leader transfer aborted or not
  wp_join iprop(∃ (s1 s2 : NState), "Hphys" ∷ ownRaftPhysCV c c.voters r id s2 ∗
      "Hghost" ∷ ownStepGhost γ md c id s2 ∗
      "%Hs1" ∷ ⌜(NStateWf s2 ∧
        (uint.Z s.logst.committed ≤ uint.Z s2.logst.committed ∧
          PVoteLe (toPState s) (toPState s2)) ∧
        (∀ s', TickStep s2 s' → TickStep s s')) ∧
        -- (Q8 stage 1 slice 12) the trace mode kept, and the abort
        s2.gh = s.gh ∧ (s2 = s1 ∨ s2 = { s1 with lt := W64 0 })⌝ ∗
      "HG" ∷ ((⌜s1 = s⌝ ∗ R.G) ∨ Gm s1) ∗
      "r" ∷ r_ptr ↦ r) with [Hphys Hghost r Hlc2 HG Hgcq]
    as ⟨%s1, %s2, Hphys, Hghost, %Hs1, HG, r⟩
  · wp_apply raft.wp_store_electionElapsedC $$ Hphys as Hphys
    wp_apply raft.wp_load_checkQuorumC $$ Hphys as Hphys
    cases Hcq : s.cq
    · -- no quorum check: the caller's `R.G` kept
      try wp_auto
      wp_apply raft.wp_load_stateC $$ Hphys as Hphys
      cases Hrole : s.role
      all_goals simp (config := { decide := true }) only [
        decide_false, _root_.decide_true]
      all_goals try wp_auto
      rotate_left 2
      · -- a leader: abort a transfer in progress
        wp_apply raft.wp_load_leadTransfereeC $$ Hphys as Hphys
        by_cases Hlt : s.lt = W64 0
        · rw [decide_eq_true Hlt]
          try wp_auto
          wp_join_done
          iexists s, s
          iframe Hphys Hghost r
          isplitr
          · ipureintro
            exact ⟨⟨Hwf, ⟨Int.le_refl _, PVoteLe.refl _⟩, fun _ h => h⟩, rfl, .inl rfl⟩
          ileft; iframe HG; ipureintro; rfl
        · rw [decide_eq_false Hlt]
          try wp_auto
          wp_apply wp_raft_abortLeaderTransfer c (V := c.voters) $$ [$Hphys] as Hphys
          try wp_auto
          wp_join_done
          ihave Hghost := ownStepGhost_congr γ md c id (s := s) (s' := { s with lt := W64 0 }) rfl rfl rfl rfl $$ Hghost
          iexists s, { s with lt := W64 0 }
          iframe Hphys Hghost r
          isplitr
          · ipureintro
            exact ⟨⟨Hwf, ⟨Int.le_refl _, PVoteLe.refl _⟩, fun _ h => h⟩, rfl, .inr rfl⟩
          ileft; iframe HG; ipureintro; rfl
      all_goals
        wp_join_done
        iexists s, s
        iframe Hphys Hghost r
        isplitr
        · ipureintro
          exact ⟨⟨Hwf, ⟨Int.le_refl _, PVoteLe.refl _⟩, fun _ h => h⟩, rfl, .inl rfl⟩
        ileft; iframe HG; ipureintro; rfl
    · -- (2026-10-17) `checkQuorum` on: `r.Step(&pb.Message{From: new(r.id), Type:
      -- pb.MsgCheckQuorum.Enum()})`, built as the `MsgBeat` below; the leader may step down
      try wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      try wp_auto
      haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
      wp_apply wp_MessageType_Enum (W32 12)
      iintro %pty Hpty
      imod cellRO_alloc $$ Hpty with #cTy
      imod cellRO_alloc $$ «$v0» with #cFr
      wp_auto
      ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod ownSlice_persist $$ Hnilb with #Hnilb
      ihave Hnile : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod ownSlice_persist $$ Hnile with #Hnile
      ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
      · iapply ownSlice_nil
      imod msgPtsC_of_struct «$a0_ptr»
          { state' := zeroValDef, Type' := pty, To' := null, From' := «$v0_ptr», Term' := null,
            LogTerm' := null, Index' := null, Entries' := slice.nil, Commit' := null, Vote' := null,
            Snapshot' := null, Reject' := null, RejectHint' := null, Context' := slice.nil,
            Responses' := slice.nil, unknownFields' := slice.nil, sizeCache' := 0 }
          DFrac.discard true [] ⟨{ (zero_val MessageM) with Type' := W32 12, From' := id }, [], none, [], []⟩
          ⊤ rfl $$ [«$a0» Hnilr] with Hmsg
      · iframe «$a0» Hnile Hnilb Hnilr cTy cFr
        simp only [snapOpt, ↓reduceIte]
        repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
        isplitr
        · iapply BigSepL2.bigSepL2_nil.2; itrivial
        isplitr
        · iapply ownSliceCap_nil
        itrivial
      have hP : (tickMsg MsgCheckQuorum id).Type' ≠ MsgProp := by simp [MsgCheckQuorum, MsgProp]
      imod rdCred_zero_upd (GF := GF) γ with Hcr
      ihave ⟨Hgates, Hclose⟩ := Hgcq $$ %rfl
      wp_apply wp_raft_Step c md γ r id s «$a0_ptr» (tickMsg MsgCheckQuorum id) [] [] none [] R Gm
          (by simp [StepMsg, stepMsgTypes, MsgCheckQuorum])
          (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
          (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (fun _ => rfl) (by msg_ne)
          (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
          (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
          (GMode.Pre.of_other (by msg_ne) Hpc (by msg_ne) (by msg_ne))
          (fun h => absurd h (by msg_ne))
          (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne))
          (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne))
        $$ [$Hphys $Hghost $Hlc2 Hcr Hmsg $HG $Hgates $Hclose]
      · simp only [hP, ↓reduceIte, named]
        ihave Hmsg := msgIn_of_msgPtsC_cap _ _ _ $$ Hmsg
        isplitr
        · imodintro; iintro %Hc; exact absurd Hc.1 (by msg_ne)
        isplitl [Hmsg]
        · rw [show (msgIn «$a0_ptr» DFrac.discard ⟨tickMsg MsgCheckQuorum id, [], none, [], []⟩ : IProp GF) =
              msgIn «$a0_ptr» DFrac.discard ⟨{ (zero_val MessageM) with Type' := W32 12, From' := id }, [], none, [], []⟩ from rfl]
          iframe Hmsg
          repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
          imodintro
          iintro %ty %Hty
          rw [show mtypeOf (tickMsg MsgCheckQuorum id).Type' = none from rfl] at Hty
          cases Hty
        isplitl [Hcr]
        · rw [ite_eq_right (by msg_ne)]; iexact Hcr
        imodintro
        iintro %Hc
        simp [MsgSnap, MsgCheckQuorum] at Hc
      simp only [hP]
      iintro %err %s0 %c' %md' ⟨Hphys, Hghost, %Hwf0, %Href, %Hcc, -, %Hfr, -, %Htm, -, -, -, Herr, HG⟩
      have Hcm0 := And.intro Href.commit_mono Href.voteLe
      have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
      have e2 := Hcc (by msg_ne); subst c'
      -- the step keeps the term and the log's frame: a tick from `s0` is one from `s`
      have Htr0 : ∀ s', TickStep s0 s' → TickStep s s' := by
        obtain ⟨Ht1, -, Ht3, Hi, -, -⟩ := Htm (by msg_ne)
        have Ht3 := Ht3 (by msg_ne) (by msg_ne) (by msg_ne)
        have H0 : uint.Z (tickMsg MsgCheckQuorum id).Term' = 0 := rfl
        simp only [H0] at Ht3
        have h0 : 0 ≤ uint.Z s.term := by word
        rw [Int.max_eq_left h0] at Ht3
        have Hi := Hi (by msg_ne)
        have Hf := Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne))
        have Heq : s0.term = s.term := by word
        intro s' ⟨Hf', Hl', Hu', Hi', Hp', Hg', Hs'⟩
        exact ⟨Hf.trans Hf', by omega, by omega, by omega, fun h => (Hp' h).trans Heq,
          fun fp hg => Hg' fp (PreGuardF.step (Htm (by msg_ne)) hg),
          fun h1 h2 => (Htm (by msg_ne)).2.2.2.2.2.2 (Hs' h1 h2).1 (Hs' h1 h2).2⟩
      icases Herr with (%Herr | ⟨%Hc', -⟩)
      rotate_left
      · exfalso; revert Hc'; msg_ne
      subst Herr
      wp_auto
      wp_apply raft.wp_load_stateC $$ Hphys as Hphys
      cases Hrole : s0.role
      all_goals simp (config := { decide := true }) only [
        decide_false, _root_.decide_true]
      all_goals try wp_auto
      rotate_left 2
      · -- a leader: abort a transfer in progress
        wp_apply raft.wp_load_leadTransfereeC $$ Hphys as Hphys
        by_cases Hlt : s0.lt = W64 0
        · rw [decide_eq_true Hlt]
          try wp_auto
          wp_join_done
          iexists s0, s0
          iframe Hphys Hghost r
          isplitr
          · ipureintro
            exact ⟨⟨Hwf0, Hcm0, Htr0⟩,
              NetFrame.ns (Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun _ => trivial)), .inl rfl⟩
          iright; iexact HG
        · rw [decide_eq_false Hlt]
          try wp_auto
          wp_apply wp_raft_abortLeaderTransfer c (V := c.voters) $$ [$Hphys] as Hphys
          try wp_auto
          wp_join_done
          ihave Hghost := ownStepGhost_congr γ _ c id (s := s0) (s' := { s0 with lt := W64 0 }) rfl rfl rfl rfl $$ Hghost
          iexists s0, { s0 with lt := W64 0 }
          iframe Hphys Hghost r
          isplitr
          · ipureintro
            exact ⟨⟨Hwf0, Hcm0, Htr0⟩,
              NetFrame.ns (Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun _ => trivial)), .inr rfl⟩
          iright; iexact HG
      all_goals
        wp_join_done
        iexists s0, s0
        iframe Hphys Hghost r
        isplitr
        · ipureintro
          exact ⟨⟨Hwf0, Hcm0, Htr0⟩,
            NetFrame.ns (Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun _ => trivial)), .inl rfl⟩
        iright; iexact HG
  · -- the election timeout not passed: the caller's `R.G` kept
    iexists s, s
    iframe Hphys Hghost r
    isplitr
    · ipureintro
      exact ⟨⟨Hwf, ⟨Int.le_refl _, PVoteLe.refl _⟩, fun _ h => h⟩, rfl, .inl rfl⟩
    ileft; iframe HG; ipureintro; rfl
  obtain ⟨⟨Hwf1, Hcm1, Htr⟩, Hgh2, Hs12⟩ := Hs1
  -- no quorum check: the caller's `Gm s` (`"Hskip"`)
  have Hm : ∀ (A : IProp GF) (B : NState → IProp GF) (s s1 : NState),
      (((⌜s1 = s⌝ ∗ A) ∨ B s1) ∗ (A ={⊤}=∗ B s) : IProp GF) ⊢ |={⊤}=> B s1 := by
    intro A B s s1
    iintro ⟨(⟨%h, HA⟩ | HB), Hk⟩
    · subst h; iapply Hk; iexact HA
    · imodintro; iexact HB
  ihave HG := Hm R.G Gm s s1 $$ [HG Hskip]
  · iframe HG Hskip
  imod HG
  -- `if r.state != StateLeader { return }`
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  cases Hrole : s2.role
  all_goals
    simp (config := { decide := true }) only [
      decide_false, _root_.decide_true]
    try wp_auto
  all_goals try (
    iapply HΦ $$ %s2
    iframe Hphys Hghost
    isplitr; · ipureintro; exact Hwf1
    isplitr; · ipureintro; exact Hcm1
    isplitr; · ipureintro; exact Htr _ (TickStep.refl s2)
    ileft
    iexists s1
    iframe HG
    ipureintro; exact Hs12)
  -- a leader: past the heartbeat timeout, `r.heartbeatElapsed = 0` and
  -- `r.Step(pb.Message{From: r.id, Type: MsgBeat})`
  wp_apply raft.wp_load_heartbeatElapsedC $$ Hphys as %v5 Hphys
  wp_apply raft.wp_load_heartbeatTimeoutC $$ Hphys as %v6 Hphys
  by_cases Hhb : sint.Z v6 ≤ sint.Z v5
  · rw [decide_eq_true Hhb]
    wp_auto
    wp_apply raft.wp_store_heartbeatElapsedC $$ Hphys as Hphys
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    try wp_auto
    -- (raft v3.7, stage R4) `&pb.Message{From: new(r.id), Type: pb.MsgBeat.Enum()}`, built into
    -- `msgIn` (`msgPtsC_of_struct`), its two cells frozen
    -- (as `confchange/toConfChangeSingle.lean`) Perennial gives `NotInterface` per type
    -- constructor, and `go.int32` (`MessageType`'s underlying type) is a non-reducible definition
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 1)
    iintro %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    imod cellRO_alloc $$ «$v0» with #cFr
    wp_auto
    ihave Hnilb : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSlice_persist $$ Hnilb with #Hnilb
    ihave Hnile : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSlice_persist $$ Hnile with #Hnile
    ihave Hnilr : (slice.nil ↦* ([] : List Loc) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod msgPtsC_of_struct «$a0_ptr»
        { state' := zeroValDef, Type' := pty, To' := null, From' := «$v0_ptr», Term' := null,
          LogTerm' := null, Index' := null, Entries' := slice.nil, Commit' := null, Vote' := null,
          Snapshot' := null, Reject' := null, RejectHint' := null, Context' := slice.nil,
          Responses' := slice.nil, unknownFields' := slice.nil, sizeCache' := 0 }
        DFrac.discard true [] ⟨{ (zero_val MessageM) with Type' := W32 1, From' := id }, [], none, [], []⟩
        ⊤ rfl $$ [«$a0» Hnilr] with Hmsg
    · iframe «$a0» Hnile Hnilb Hnilr cTy cFr
      simp only [snapOpt, ↓reduceIte]
      repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
      isplitr
      · iapply ownSliceCap_nil
      itrivial
    have hP : (tickMsg MsgBeat id).Type' ≠ MsgProp := by simp [MsgBeat, MsgProp]
    imod rdCred_zero_upd (GF := GF) γ with Hcr
    -- the caller's resources for the heartbeat's `Step`, from `Gm s1`
    have Hb : s2.gh = s.gh ∧ s2.role = .leader ∧ (s2 = s1 ∨ s2 = { s1 with lt := W64 0 }) :=
      ⟨Hgh2, Hrole, Hs12⟩
    imod Hgbeat $$ %s1 %s2 %Hb HG with ⟨%R2, HG, Hgates, Hclose⟩
    wp_apply wp_raft_Step c md γ r id s2 «$a0_ptr» (tickMsg MsgBeat id) [] [] none [] R2 Gout
        (by simp [StepMsg, stepMsgTypes, MsgBeat])
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (fun _ => rfl) (by msg_ne)
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
        (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf1
        (GMode.Pre.of_other (by msg_ne) (GMode.Guard.of_nonpre (fun _ => by rw [Hrole]; decide))
          (by msg_ne) (by msg_ne))
        (fun h => absurd h (by msg_ne))
        (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne))
        (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne))
      $$ [$Hphys $Hghost $Hlc1 Hcr Hmsg $HG $Hgates $Hclose]
    · simp only [hP, ↓reduceIte, named]
      ihave Hmsg := msgIn_of_msgPtsC_cap _ _ _ $$ Hmsg
      isplitr
      · imodintro; iintro %Hc; exact absurd Hc.1 (by msg_ne)
      isplitl [Hmsg]
      · rw [show (msgIn «$a0_ptr» DFrac.discard ⟨tickMsg MsgBeat id, [], none, [], []⟩ : IProp GF) =
            msgIn «$a0_ptr» DFrac.discard ⟨{ (zero_val MessageM) with Type' := W32 1, From' := id }, [], none, [], []⟩ from rfl]
        iframe Hmsg
        repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
        imodintro
        iintro %ty %Hty
        rw [show mtypeOf (tickMsg MsgBeat id).Type' = none from rfl] at Hty
        cases Hty
      isplitl [Hcr]
      · rw [ite_eq_right (by msg_ne)]; iexact Hcr
      imodintro
      iintro %Hc
      simp [MsgSnap, MsgBeat] at Hc
    simp only [hP]
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, -, %Htm, -, -, -, Herr, HG⟩
    have Hcm := And.intro Href.commit_mono Href.voteLe
    have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
    have e2 := Hcc (by msg_ne); subst c'
    icases Herr with (%Herr | ⟨%Hc', -⟩)
    · subst Herr
      wp_auto
      iapply HΦ $$ %s'
      iframe Hphys Hghost
      isplitr; · ipureintro; exact Hwf'
      isplitr; · ipureintro; exact ⟨Int.le_trans Hcm1.1 Hcm.1, Hcm1.2.trans Hcm.2⟩
      isplitr
      rotate_left
      · iright; iexact HG
      ipureintro
      obtain ⟨Ht1, -, Ht3, Hi, -, Hpc'⟩ := Htm (by msg_ne)
      have Ht3 := Ht3 (by msg_ne) (by msg_ne) (by msg_ne)
      have H0 : uint.Z (tickMsg MsgBeat id).Term' = 0 := rfl
      simp only [H0] at Ht3
      exact Htr _ ⟨Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)), Ht1,
        by have h0 : 0 ≤ uint.Z s2.term := by word
           rw [Int.max_eq_left h0] at Ht3; omega,
        Hi (by msg_ne), fun h => (Hpc'.1 h).1, fun _ hg => PreGuardF.step (Htm (by msg_ne)) hg,
        Hpc'.2⟩
    · exfalso; revert Hc'; msg_ne
  · rw [decide_eq_false Hhb]
    wp_auto
    iapply HΦ $$ %s2
    iframe Hphys Hghost
    isplitr; · ipureintro; exact Hwf1
    isplitr; · ipureintro; exact Hcm1
    isplitr; · ipureintro; exact Htr _ (TickStep.refl s2)
    ileft
    iexists s1
    iframe HG
    ipureintro; exact Hs12

end proof

end EtcdGrove
end Perennial
