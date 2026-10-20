/-
Port of election_proof/proof_stepCandidate.v.
-/
module

public import Spec.go_etcd_io.raft.v3.stepCandidate
public import Spec.go_etcd_io.raft.v3.raft__pollAndReportDiff
public import Spec.go_etcd_io.raft.v3.raft__getWitnessVoteRequestReadiness
public import Spec.go_etcd_io.raft.v3.raft__sendRequestVoteToWitness
public import Proof.go_etcd_io.raft.v3.LemmasWitnessR
public import Spec.go_etcd_io.raft.v3.raft__becomeLeader
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.raft__bcastAppend
public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__handleSnapshot
public import Spec.go_etcd_io.raft.v3.raft__campaign
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [FfiSyntax] ffi [FfiInterp ffi] [FfiSemantics ext ffi] [GoGlobalContext] in
/-- One vote short (`votesToWin = 1`): `quorum - 1` granted votes. -/
theorem votesToWin_one {S : GSet w64} {votes : GMap w64 Bool}
    (h : W64 (votesToWin S votes : Int) = W64 1) (hs : (GMap.size S : Int) ≤ 2 ^ 62) :
    GMap.size S / 2 ≤ GMap.size (granted votes ∩ S) := by
  have hle : votesToWin S votes ≤ GMap.size S / 2 + 1 := by
    unfold votesToWin; split <;> omega
  have h1 : (votesToWin S votes : Int) = 1 := by
    have := congrArg (fun x : w64 => uint.Z x) h
    try simp only at this
    rw [uint_Z_W64 _ (by omega) (by omega)] at this
    exact this
  unfold votesToWin at h1
  split at h1 <;> omega


set_option hygiene false in
/-- The request itself, at the struct re-sealed: the type and term by `r.state`, then
`sendRequestVoteToWitness`; the body ends with it queued. -/
local macro "wvp_pure" : tactic => `(tactic| (
  first
  | trivial
  | exact ⟨by omega, fun _ => rfl, Or.inl rfl⟩
  | exact ⟨fun _ => rfl, Or.inl rfl⟩
  | exact ⟨by omega, Or.inl rfl⟩
  | exact Or.inl rfl
  | (refine ⟨?_, ?_, ?_⟩ <;> first | trivial | omega | exact fun _ => rfl | exact Or.inl rfl)))

set_option hygiene false in
local macro "wvp_send" : tactic => `(tactic| (
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  first
  | (rw [decide_eq_true (by simp only [Hrole]; decide)])
  | (rw [decide_eq_false (by simp only [Hrole]; decide)])
  try rw [show raftpb.MsgVote = #MsgVote from rfl]
  try rw [show raftpb.MsgPreVote = #MsgPreVote from rfl]
  try wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  try wp_auto
  wp_apply wp_raft_sendRequestVoteToWitness c _ r id _ c.wit _ _ Hw $$ [Hphys]
    as %ls ⟨Hphys, %Hls⟩
  · iframe
  unfold forMapPostcondition
  iright; ileft
  isplitr
  · ipureintro; first | rfl | trivial
  iexists _, _, _
  simp only [named]
  iframe
  ipureintro
  exact ⟨by omega, fun h => absurd h (by omega),
    Or.inr ⟨ls, Hw, Hout, votesToWin_one (Hrdy.2.1 rfl) Hinsz, Hls, rfl⟩⟩))

set_option hygiene false in
/-- After `poll` (2026-10-20, W3b-C): `if r.trk.Witnesses[0] != 0 || r.trk.Witnesses[1] != 0`, the
witnesses `[c.wit, 0]`, then one of two log lines, which read `r.id`, the message type and the
logger; joined. -/
local macro "wvp_logline" : tactic => `(tactic| (
  wp_join at next with [Hphys Hm r m gr rj rv]
  · wp_apply raft.wp_load_trk_witnessC' c r id _ (W64 0) (by decide) $$ Hphys as Hphys
    rw [witOf_zero]
    by_cases Hwl : c.wit = W64 0
    · rw [Hwl]
      try wp_auto
      wp_apply raft.wp_load_trk_witnessC' c r id _ (W64 1) (by decide) $$ Hphys as Hphys
      rw [witOf_one]
      try wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply wp_GetType.1 ml _ _ _ _ $$ [Hm] as Hm
      · iframe
      wp_raft_logC
      wp_join_done
    · try wp_auto
      first
      | rw [decide_eq_false Hwl]
      | simp only [decide_eq_false Hwl]
      try wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply wp_GetType.1 ml _ _ _ _ $$ [Hm] as Hm
      · iframe
      wp_raft_logC
      wp_join_done))

set_option hygiene false in
/-- `quorum.VotePending` (2026-10-20, witness support, W3b-C): the witnesses ready to vote
(`getWitnessVoteRequestReadiness`: none, or `{c.wit ↦ ready}`), and for one that is and has not
been asked (`r.witnessVoteAsked`), the request (`sendRequestVoteToWitness`) of type `vt` and term
`tm`. Leaves the pure goal of `HΦ` with the queued requests `wq` and their `WitAsk` fact `HwqF`. -/
local macro "wvp_loop " vt:term:max tm:term:max : tactic => `(tactic| (
  icases ownRaftPhysC_witSimple c r id _ $$ Hphys with ⟨%Hsimple, Hphys⟩
  icases ownRaftPhysC_incoming_size c r id _ $$ Hphys with ⟨%Hinsz, Hphys⟩
  wp_apply wp_raft_getWitnessVoteRequestReadiness c _ r id _ d _ _ Hd $$ [Hphys]
    as %mref ⟨Hphys, Hrd⟩
  · iframe
  icases Hrd with (⟨%Hnil, -⟩ | ⟨%ready, Hm, %Hrdy⟩)
  focus (
    -- no witness ready: nothing to range over
    subst Hnil
    wp_apply (wp_map_nil_for_range_val ⟨_, _, _⟩)
    wp_pures; (try wp_auto)
    iapply HΦ $$ %GoInterface.nil %_ %false %c
    rw [← sendMsgs_nil { s with votes := recordVote s.votes m.From' (!m.Reject') }]
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    have HwqF : WitAsk c id $vt $tm s (recordVote s.votes m.From' (!m.Reject')) [] := Or.inl rfl
    generalize ([] : List Msg) = wq at HwqF ⊢
    )
  rotate_left
  focus (
    -- the witness, ready or not
    have Hw : c.wit ≠ W64 0 := Hrdy.1
    have Hout : c.outgoing = ∅ := Hsimple Hw
    try wp_auto
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : Bool) (y : w64)
        (wq : List Msg),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "%Hwq" ∷ ⌜(i = 0 → wq = []) ∧
          WitAsk c id $vt $tm s (recordVote s.votes m.From' (!m.Reject')) wq⌝ ∗
        "ready" ∷ ready_ptr ↦ x ∗ "witnessID" ∷ witnessID_ptr ↦ y ∗ "r" ∷ r_ptr ↦ r ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id
          (sendMsgs { s with votes := recordVote s.votes m.From' (!m.Reject') } wq))) $$ Hm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [ready witnessID r Hphys]
    · iexists _, _, []
      simp only [named]
      rw [sendMsgs_nil]
      iframe
      ipureintro
      wvp_pure
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      rw [GMap.lookup_insert_eq_iff] at Hvv
      have Hkw : key = c.wit ∧ vv = ready := by
        by_cases h : c.wit = key
        · rw [if_pos h] at Hvv; cases Hvv; exact ⟨h.symm, rfl⟩
        · rw [if_neg h] at Hvv; simp at Hvv
      obtain ⟨rfl, rfl⟩ := Hkw
      rw [GMap.insert_empty, GMap.map_size_singleton] at Hklen
      have Hi0 : i = 0 := by
        have := (List.getElem?_eq_some_iff.1 Hkey).1
        omega
      obtain rfl := Hwq.1 Hi0
      subst Hi0
      rw [sendMsgs_nil]
      wp_auto
      cases vv
      · -- not ready: skipped
        wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; first | rfl | trivial
        iexists _, _, []
        simp only [named]
        rw [sendMsgs_nil]
        iframe
        ipureintro
        wvp_pure
      -- ready: asked before?
      icases ownRaftPhysC_asked c r id _ $$ Hphys with ⟨%asked, Haf, Hask, Hreseal⟩
      wp_auto
      iunfold ownAsked at Hask
      icases Hask with (%Hn | ⟨%a, Ha⟩)
      · -- never: `r.witnessVoteAsked` is nil, made now
        subst Hn
        try wp_auto
        rw [show (zero_val Bool : Bool) = false from rfl]
        try wp_auto
        wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %am Ham
        try wp_auto
        wp_apply wp_mapInsert $$ Ham as Ham
        ihave Hask : ownAsked (GF := GF) am $$ [Ham]
        · iunfold ownAsked; iright; iexists _; iexact Ham
        ihave Hphys := Hreseal $$ %am %Hw Haf Hask
        wvp_send
      · ihave %Hann := ownMap_not_nil _ _ _ $$ Ha
        wp_apply (wp_map_lookup1 go.uint64 go.bool asked a c.wit) $$ Ha as Ha
        rw [show (zero_val Bool : Bool) = false from rfl]
        cases Hac : (a !! c.wit).getD false
        · -- not yet
          simp only [Bool.not_false]
          wp_auto
          rw [decide_eq_false Hann]
          wp_auto
          wp_apply wp_mapInsert $$ Ha as Ha
          ihave Hask : ownAsked (GF := GF) asked $$ [Ha]
          · iunfold ownAsked; iright; iexists _; iexact Ha
          ihave Hphys := Hreseal $$ %asked %Hw Haf Hask
          wvp_send
        · -- asked already: skipped
          simp only [Bool.not_true]
          wp_auto
          ihave Hask : ownAsked (GF := GF) asked $$ [Ha]
          · iunfold ownAsked; iright; iexists _; iexact Ha
          ihave Hphys := Hreseal $$ %asked %Hw Haf Hask
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _, _, []
          simp only [named]
          rw [sendMsgs_nil]
          iframe
          ipureintro
          wvp_pure
    iintro HP Hm
    iNamed HP
    wp_pures; (try wp_auto)
    iapply HΦ $$ %GoInterface.nil %_ %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    have HwqF := Hwq.2)))

set_option maxHeartbeats 1000000 in
/-- By type. `MsgProp`: `Infof`, then `return ErrProposalDropped` (the global's
points-to from `isInitialized_access`). `MsgApp`: `becomeFollower(m.Term, m.From)` with
`m.Term = s.term`, then `handleAppendEntries` at the follower state. `MsgHeartbeat`: the
same `becomeFollower`, then `handleHeartbeat`. `MsgBeat`, `MsgAppResp`,
`MsgHeartbeatResp`: no arm; nor `MsgReadIndex`, `MsgReadIndexResp` (2026-10-12).

`MsgVoteResp`, unchanged since 2026-09: the type switch is walked to the
`myVoteRespType` arm (`m.Type = MsgVoteResp`, and `state = StateCandidate` so
`myVoteRespType` is `MsgVoteResp` and not `MsgPreVoteResp`), then `poll` records the
vote and the `res` switch does one of three things: win and broadcast, lose and step
down, or nothing.

Each arm lands on `voteRespResult` directly. `VoteWon` is `becomeLeader` followed by
`bcastAppend`, whose spec gives *some* `ReplSends` list rather than one `App` per peer
-- which is what `Step.win` asks for. `VoteLost` is `becomeFollower(r.Term, None)`, and
`becomeFollower s1 s1.term (W64 0)` is verbatim `voteRespResult`'s `lost` branch.
`VotePending` leaves the state at `s1` and sends nothing.

raft v3.7 (2026-10-15, stage R4): the message's fields are read by its getters (`GetType`,
`GetFrom`, `GetTerm`, `GetReject`, callees), and `MsgApp`/`MsgHeartbeat`/`MsgSnap` hand the
received message (`msgIn`, entries read-only) to their handlers. -/
theorem stepCandidate.wp_proof
    (wp_raft_poll : raft.pollAndReportDiff.spec (GF := GF) (hG := hG))
    (wp_raft_getWitnessVoteRequestReadiness :
      raft.getWitnessVoteRequestReadiness.spec (GF := GF) (hG := hG))
    (wp_raft_sendRequestVoteToWitness :
      raft.sendRequestVoteToWitness.spec (GF := GF) (hG := hG))
    (wp_raft_becomeLeader : raft.becomeLeader.spec (GF := GF) (hG := hG))
    (wp_raft_becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (wp_raft_bcastAppend : raft.bcastAppend.spec (GF := GF) (hG := hG))
    (wp_raft_handleAppendEntries : raft.handleAppendEntries.spec (GF := GF) (hG := hG))
    (wp_raft_handleHeartbeat : raft.handleHeartbeat.spec (GF := GF) (hG := hG))
    (wp_raft_handleSnapshot : raft.handleSnapshot.spec (GF := GF) (hG := hG))
    (wp_raft_campaign : raft.campaign.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetReject : raftpb.Message.GetReject.spec (GF := GF) (hG := hG)) :
    stepCandidate.spec (GF := GF) (hG := hG) := by
  intro c scfg r id s ml m ents sn rs sv cl Hty Hterm Hrole Happ Hhb Hpvnw Hsnap
  wp_start as H
  iNamed H
  -- a candidate is a voter (`ownRaftPhys`'s `Hvoter`; until 2026-10-13 a premise)
  icases ownRaftPhysC_voter c r id s $$ Hphys with ⟨%Hvoter, Hphys⟩
  have Hcfg : id ∈ c.voters := Hvoter (by rcases Hrole with h | h <;> rw [h] <;> decide)
  ihave #Hinit := isInitialized_access $$ Hpkg
  unfold isInitialized
  icases Hinit with ⟨%e1, %e2, %e3, %e4, %errPropDropped, %gr, %_, %_, %_, %_, #Hinit⟩
  iNamed Hinit
  wp_auto
  -- `myVoteRespType`: `MsgPreVoteResp` for a pre-candidate, `MsgVoteResp` for a
  -- candidate; the two arms are joined
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  have Hpre_iff : stateW64 s.role = W64 3 ↔ s.role = .preCandidate := by
    cases s.role <;> decide
  wp_join iprop(myVoteRespType_ptr ↦
      (if s.role = .preCandidate then W32 18 else W32 6))
    with [myVoteRespType] as myVoteRespType
  · rw [show raftpb.MsgPreVoteResp = #(W32 18) from rfl]
    wp_auto
    rw [ite_eq_left (Hpre_iff.1 Hif)]
    iframe myVoteRespType
    ipureintro; exact rfl
  · rw [show raftpb.MsgVoteResp = #(W32 6) from rfl]
    wp_auto
    rw [ite_eq_right (fun h => Hif (Hpre_iff.2 h))]
    iframe myVoteRespType
    ipureintro; exact rfl
  -- kept opaque below, so that the arms' `decide` rewrites find the program's
  -- comparisons and not this one
  generalize Hmvr : (if s.role = .preCandidate then W32 18 else W32 6) = mvr
  have Hmp : s.role = .preCandidate → mvr = W32 18 := by
    intro Hp; rw [← Hmvr, ite_eq_left Hp]
  have Hmc : s.role ≠ .preCandidate → mvr = W32 6 := by
    intro Hp; rw [← Hmvr, ite_eq_right Hp]
  clear Hmvr
  wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
  rcases Hty with Hty | Hty | Hty | Hty | Hty | Hty | Hty | Hty
  · -- `MsgVoteResp`: none of `MsgProp`, `MsgApp`, `MsgHeartbeat`, `MsgSnap`, so it falls
    -- through to `myVoteRespType`
    obtain ⟨Hterm', Hmnz⟩ := Hterm (Or.inl Hty)
    simp only [Hty, MsgVoteResp]
    wp_auto
    rcases Hrole with Hrole | Hrole
    rotate_left
    · -- a pre-candidate: `myVoteRespType` is `MsgPreVoteResp`; a vote response is
      -- ignored
      rw [Hmp Hrole]
      wp_auto
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      unfold CandidateStepResultC
      refine ⟨by simp [Hty, MsgVoteResp, MsgSnap], ?_⟩
      simp [Hty, Hrole, MsgVoteResp]
    rw [Hmc (by rw [Hrole]; decide)]
    wp_auto
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetReject.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_raft_poll _ _ _ _ _ _ _ $$ [$Hphys]
      as %g %rj0 %res %d ⟨Hphys, %Hres, %Hwon, %Hlost, %Hd⟩
    -- (2026-10-19, witness support) `if r.trk.Witnesses[0] != 0 || r.trk.Witnesses[1] != 0`:
    -- (2026-10-20) `[c.wit, 0]`; either log line
    try wp_auto
    wvp_logline
    rcases Hres with rfl | rfl | rfl
    · -- `quorum.VoteWon`: become leader and broadcast. `poll` does not touch the role,
      -- so we are still a candidate: not a pre-candidate, so this is `becomeLeader` and
      -- not `campaign`.
      simp only [VoteWon]
      wp_auto
      wp_apply raft.wp_load_stateC $$ Hphys as Hphys
      rw [decide_eq_false (by simp only [Hrole]; decide)]
      wp_auto
      wp_apply wp_raft_becomeLeader _ _ _ _ (by simp only [Hrole]; decide)
          (by exact Hterm' ▸ Hmnz) $$ [$Hphys]
        as %pvs1 ⟨Hphys, %Hmb⟩
      -- `bcastAppend` adds *some* list of `App`s from `id` at the current term -- not one
      -- per peer; see `Spec/raft__bcastAppend.lean`.
      wp_apply wp_raft_bcastAppend c r id _ (by rfl) $$ [$Hphys] as %ms %pvs ⟨Hphys, %Hms, %Hmm⟩
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      unfold CandidateStepResultC
      refine ⟨by simp [Hty, MsgVoteResp, MsgSnap], ?_⟩
      simp only [Hty, Hrole, ↓reduceIte]
      refine ⟨trivial, ?_⟩
      have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
      simp only [Hnp, ↓reduceIte]
      refine ⟨true, false, ms, pvs, [], fun _ => ⟨Hwon.1 rfl, ?_, ?_⟩, fun h => absurd h (by decide),
        fun h => absurd rfl h, Or.inl rfl, ?_⟩
      · exact (replSends_prvals _ _ pvs1 ms).1 Hms
      · rw [Hmm]; exact Hmb
      · rw [sendMsgs_nil]; cases s; rfl
    · -- `quorum.VoteLost`: step down at the unchanged term
      simp only [VoteLost]
      wp_auto
      -- the `r.Term` the code passes is `s1`'s term
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      wp_apply wp_raft_becomeFollower _ _ _ _ _ _ (by exact Int.le_refl _) $$ [$Hphys] as %pvs Hphys
      iapply HΦ $$ %GoInterface.nil %_ %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      unfold CandidateStepResultC
      refine ⟨by simp [Hty, MsgVoteResp, MsgSnap], ?_⟩
      simp only [Hty, Hrole, ↓reduceIte]
      refine ⟨trivial, ?_⟩
      have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
      simp only [Hnp, ↓reduceIte]
      refine ⟨false, true, [], pvs, [], fun h => absurd h (by decide), fun _ => Hlost.1 rfl,
        fun h => absurd rfl h, Or.inl rfl, ?_⟩
      rw [sendMsgs_nil]; cases s; rfl
    · -- `quorum.VotePending`: neither switch arm fires; keep waiting. (2026-10-19, witness
      -- support) No witness to ask: `getWitnessVoteRequestReadiness` is `nil`
      simp only [VotePending]
      wp_auto
      wvp_loop MsgVote s.term
      all_goals
        unfold CandidateStepResultC
        refine ⟨by simp [Hty, MsgVoteResp, MsgSnap], ?_⟩
        simp only [Hty, Hrole, ↓reduceIte]
        refine ⟨trivial, ?_⟩
        have Hnp : ¬ (PRole.candidate = PRole.preCandidate) := by decide
        simp only [Hnp, ↓reduceIte]
        -- nothing wrote a `Progress`: the values are `s1`'s own
        refine ⟨false, false, [], s.prvals, wq, fun h => absurd h (by decide),
          fun h => absurd h (by decide), fun _ => ⟨rfl, rfl⟩, HwqF, ?_⟩
        cases s; simp only at Hrole; subst Hrole; rfl
  · -- `MsgProp`: no leader to forward to; dropped
    simp only [Hty, MsgProp]
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_raft_logC
    iapply HΦ $$ %errPropDropped %s %true %c
    iframe Hphys
    simp only [↓reduceIte]
    isplitr
    · ipureintro
      unfold CandidateStepResultC
      refine ⟨by simp [Hty, MsgProp, MsgSnap], ?_⟩
      simp [Hty, MsgVoteResp, MsgProp]
    iexact ErrPropDropped
  · -- `MsgApp`: `becomeFollower(m.Term, m.From)`, then `handleAppendEntries`
    obtain ⟨Hwf, Hnw, Hconf, Hfid⟩ := Happ Hty
    have Hterm' := (Hterm (Or.inr (Or.inl Hty))).1
    rw [show (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) = DFrac.discard by
      simp [Hty, MsgApp, MsgProp]]
    simp only [Hty, MsgApp]
    wp_auto
    wp_apply wp_GetTerm.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_raft_becomeFollower _ _ _ _ _ _
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) $$ [$Hphys]
      as %pvs Hphys
    wp_apply wp_raft_handleAppendEntries _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs }
      ml m ents sn cl rs Hwf Hnw Hconf Hfid Hty (fun h => by simp [becomeFollower] at h) $$ [$Hphys $Hm]
      as %s' ⟨Hphys, %Hres⟩
    iapply HΦ $$ %GoInterface.nil %s' %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    unfold CandidateStepResultC
    refine ⟨by simp [Hty, MsgApp, MsgSnap], ?_⟩
    simp only [Hty, MsgVoteResp, MsgProp, MsgApp]
    refine ⟨trivial, pvs, ?_⟩
    rw [← Hterm']
    exact Hres
  · -- `MsgHeartbeat`: `becomeFollower(m.Term, m.From)`, then `handleHeartbeat`
    obtain ⟨Hcommit, Hfrom⟩ := Hhb Hty
    have Hterm' := (Hterm (Or.inr (Or.inr (Or.inl Hty)))).1
    simp only [Hty, MsgHeartbeat]
    wp_auto
    wp_apply wp_GetTerm.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_raft_becomeFollower _ _ _ _ _ _
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) $$ [$Hphys]
      as %pvs Hphys
    wp_apply wp_raft_handleHeartbeat _ _ _ { becomeFollower s m.Term' m.From' with prvals := pvs }
      ml _ _ _ m ents sn cl rs Hcommit Hfrom $$ [$Hphys $Hm] as ⟨Hphys, -⟩
    iapply HΦ $$ %GoInterface.nil %_ %false %c
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    unfold CandidateStepResultC
    refine ⟨by simp [Hty, MsgHeartbeat, MsgSnap], ?_⟩
    simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat]
    refine ⟨trivial, pvs, ?_⟩
    rw [← Hterm']
  · -- `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`: no arm; `myVoteRespType` is one of
    -- the two response types, neither of these
    rcases Hty with Hty' | Hty' | Hty' | Hty' <;> rw [Hty'] <;>
      simp only [MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum] <;> wp_auto
    all_goals
      by_cases Hp : s.role = .preCandidate
      · rw [Hmp Hp]
        wp_auto
        iapply HΦ $$ %GoInterface.nil %s %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        unfold CandidateStepResultC
        refine ⟨by simp [Hty', MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap], ?_⟩
        simp [Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum]
      · rw [Hmc Hp]
        wp_auto
        iapply HΦ $$ %GoInterface.nil %s %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        unfold CandidateStepResultC
        refine ⟨by simp [Hty', MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap], ?_⟩
        simp [Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum]
  · -- `MsgSnap`: `becomeFollower(m.Term, m.From)`, then `handleSnapshot`
    have Hterm' := (Hterm (Or.inr (Or.inr (Or.inr Hty)))).1
    obtain ⟨Hsn, Hscfg, Hscope, Hcfg', Hfid, Hns, Hw0⟩ := Hsnap Hty
    rw [show (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) = DFrac.discard by
      simp [Hty, MsgSnap, MsgProp]]
    simp only [Hty, MsgSnap]
    wp_auto
    wp_apply wp_GetTerm.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
    wp_apply wp_raft_becomeFollower _ _ _ _ _ _
      (by exact Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hterm'.symm)) $$ [$Hphys]
      as %pvs Hphys
    -- (2026-10-14) at any configuration: `handleSnapshot` on the struct at `c`
    wp_apply wp_raft_handleSnapshot c _ _ { becomeFollower s m.Term' m.From' with prvals := pvs }
        ml m ents sn cl rs sv scfg rfl rfl Hsn Hscfg Hcfg' Hscope Hfid Hns Hw0 $$ [$Hphys $Hm]
      as %s' %c' ⟨Hphys, %Hres, %Hc'⟩
    iapply HΦ $$ %GoInterface.nil %s' %false %c'
    iframe Hphys
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro
    refine ⟨?_, trivial⟩
    unfold CandidateStepResultC
    refine ⟨by rw [ite_eq_left Hty]; exact Hc', ?_⟩
    simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
      MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap]
    refine ⟨trivial, pvs, ?_⟩
    rw [← Hterm']
    exact Hres
  · -- `MsgPreVoteResp` (2026-10-04)
    simp only [Hty, MsgPreVoteResp]
    wp_auto
    rcases Hrole with Hrole | Hrole
    · -- a candidate: `myVoteRespType` is `MsgVoteResp`; a stale pre-vote response,
      -- ignored
      rw [Hmc (by rw [Hrole]; decide)]
      wp_auto
      iapply HΦ $$ %GoInterface.nil %s %false %c
      iframe Hphys
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro
      refine ⟨?_, trivial⟩
      unfold CandidateStepResultC
      refine ⟨by simp [Hty, MsgSnap, MsgPreVoteResp], ?_⟩
      simp [Hty, Hrole, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
        MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp]
    · -- a pre-candidate: `poll`, then win, lose or wait
      rw [Hmp Hrole]
      wp_auto
      wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_GetType.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_GetReject.1 ml _ _ _ _ $$ [$Hm] as Hm
      wp_apply wp_raft_poll _ _ _ _ _ _ _ $$ [$Hphys]
        as %g %rj0 %res %d ⟨Hphys, %Hres, %Hwon, %Hlost, %Hd⟩
      -- (2026-10-19, witness support) `if r.trk.Witnesses[0] != 0 || r.trk.Witnesses[1] != 0`:
      -- (2026-10-20) `[c.wit, 0]`; either log line
      try wp_auto
      wvp_logline
      have Hres_pv : ∀ (s' : NState) (won lost : Bool) (peers : List w64)
          (pvs : GMap w64 Progress) (wq : List Msg),
          (won = true → JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∧
            peers ≡ₚ elements (campSet c id)) →
          (lost = true →
            JLost c (recordVote s.votes m.From' (!m.Reject'))) →
          (wq ≠ [] → won = false ∧ lost = false) →
          WitAsk c id MsgPreVote (s.term + W64 1) s (recordVote s.votes m.From' (!m.Reject')) wq →
          s' = sendMsgs { prevoteRespResult id s m.From' m.Reject' won lost peers with prvals := pvs }
            wq →
          CandidateStepResultC c scfg id s m ents sv false s' c cl := by
        intro s' won lost peers pvs wq Hw Hl Hq Hwq Hs'
        have HP : PrecandVoteRespResultC c id s m s' := ⟨won, lost, peers, pvs, wq, Hw, Hl, Hq, Hwq, Hs'⟩
        unfold CandidateStepResultC
        refine ⟨by simp [Hty, MsgSnap, MsgPreVoteResp], ?_⟩
        generalize PrecandVoteRespResultC c id s m s' = P at HP
        simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat,
          MsgBeat, MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, Hrole]
        simp
        exact HP
      rcases Hres with rfl | rfl | rfl
      · -- `quorum.VoteWon`: the real election, `campaign(campaignElection)`
        simp only [VoteWon]
        wp_auto
        wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        rw [decide_eq_true (by simp only [Hrole]; decide)]
        wp_auto
        have Hnl1 : s.role ≠ .leader := by rw [Hrole]; decide
        have Hnw1 := Hpvnw Hrole Hty
        rw [show go_etcd_io.raft.v3.campaignElection = #campaignElection from rfl]
        wp_apply wp_raft_campaign _ _ _ { s with votes := recordVote s.votes m.From' (!m.Reject') }
            _ Hnl1 Hcfg Hnw1
            (fun h => by
              have := congrArg List.length h
              simp [campaignElection, campaignPreElection] at this)
            $$ [$Hphys]
          as %peers %pvs ⟨%Hpeers, Hphys⟩
        iapply HΦ $$ %GoInterface.nil %_ %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        refine Hres_pv _ true false peers pvs [] (fun _ => ⟨Hwon.1 rfl, Hpeers⟩)
          (fun h => absurd h (by decide)) (fun h => absurd rfl h) (Or.inl rfl) ?_
        rw [sendMsgs_nil]
        have Htc : transferCtx campaignElection = [] := by
          simp (config := {decide := true}) [transferCtx, campaignElection, campaignTransfer]
        rw [Htc]
        rfl
      · -- `quorum.VoteLost`: step down at the unchanged term
        simp only [VoteLost]
        wp_auto
        wp_apply raft.wp_load_TermC $$ Hphys as Hphys
        wp_apply wp_raft_becomeFollower _ _ _ _ _ _ (by exact Int.le_refl _) $$ [$Hphys]
          as %pvs Hphys
        iapply HΦ $$ %GoInterface.nil %_ %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        exact Hres_pv _ false true [] pvs [] (fun h => absurd h (by decide)) (fun _ => Hlost.1 rfl)
          (fun h => absurd rfl h) (Or.inl rfl) (sendMsgs_nil _).symm
      · -- `quorum.VotePending`: keep waiting; no witness to ask
        simp only [VotePending]
        wp_auto
        wvp_loop MsgPreVote (s.term + W64 1)
        all_goals
          refine Hres_pv _ false false [] s.prvals wq (fun h => absurd h (by decide))
            (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl⟩) HwqF ?_
          cases s; rfl

  · -- `MsgReadIndex`, `MsgReadIndexResp` (2026-10-12), and (2026-10-13) `MsgForgetLeader`,
    -- `MsgTransferLeader` and the local reports: no arm; `MsgTimeoutNow`: logged. In each case
    -- `myVoteRespType` is one of the two vote response types, neither of these
    rcases Hty with Hty' | Hty' | Hty' | Hty' | Hty' | Hty' | Hty' <;> rw [Hty'] <;>
      simp only [MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgTransferLeader,
        MsgTimeoutNow, MsgUnreachable, MsgSnapStatus] <;> wp_auto
    all_goals
      by_cases Hp : s.role = .preCandidate
      · rw [Hmp Hp]
        wp_auto
        try (
          wp_apply raft.wp_load_idC $$ Hphys as Hphys
          wp_apply raft.wp_load_TermC $$ Hphys as Hphys
          wp_apply raft.wp_load_stateC $$ Hphys as Hphys
          wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
          wp_raft_logC)
        iapply HΦ $$ %GoInterface.nil %s %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        unfold CandidateStepResultC
        refine ⟨by simp [Hty', MsgSnap, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgTransferLeader, MsgTimeoutNow, MsgUnreachable, MsgSnapStatus], ?_⟩
        simp [Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
      · rw [Hmc Hp]
        wp_auto
        try (
          wp_apply raft.wp_load_idC $$ Hphys as Hphys
          wp_apply raft.wp_load_TermC $$ Hphys as Hphys
          wp_apply raft.wp_load_stateC $$ Hphys as Hphys
          wp_apply wp_GetFrom.1 ml _ _ _ _ $$ [$Hm] as Hm
          wp_raft_logC)
        iapply HΦ $$ %GoInterface.nil %s %false %c
        iframe Hphys
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro
        refine ⟨?_, trivial⟩
        unfold CandidateStepResultC
        refine ⟨by simp [Hty', MsgSnap, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgTransferLeader, MsgTimeoutNow, MsgUnreachable, MsgSnapStatus], ?_⟩
        simp [Hty', MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat,
          MsgAppResp, MsgHeartbeatResp, MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
          MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow]
end proof

end EtcdGrove
end Perennial
