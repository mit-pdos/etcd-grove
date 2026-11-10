/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 11 (2026-11-10): what `raft.Step`'s proof and its
untraced instance need of its gates (`LemmasStepGates.lean`; `notes/decisions.md`, "Q8 stage 1 (slice
11)"):
- `traceReceiveMessage.gated`: the receive hook's spec at `Step`'s entry, from `traceReceiveMessage.spec`,
  with the caller's gate (`HookGateOpt`, as `raft.send`'s) and the message as `Step` holds it (`msgIn`);
  raft's state and the message lent to the hook when traced (`raftLend_sep`, `msgLend_sep_some`);
- the gates of an untraced node (`stepGates_none` and the bundles'), every resource one `X`, from the
  struct's nil logger: `raft.Step.untraced` and `raft.appliedTo` (through `wp_Step_MsgProp`) use them.
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasStepGates
public import Proof.go_etcd_io.raft.v3.TracedUntraced

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The preamble keeps the ghost fields. -/
theorem preState_gh (s : NState) (m : MessageM) (pvs : GMap w64 Progress) :
    (preState s m pvs).gh = s.gh := by
  unfold preState; split <;> rfl

/-- ... and the log. -/
theorem preState_logst (s : NState) (m : MessageM) (pvs : GMap w64 Progress) :
    (preState s m pvs).logst = s.logst := by
  unfold preState; split <;> rfl

theorem preState_bf {s : NState} {m : MessageM} (h : PreBF m s) (pvs : GMap w64 Progress) :
    preState s m pvs = { becomeFollower s m.Term' (preLead m) with prvals := pvs } := by
  simp only [preState, h, ↓reduceIte]

theorem preState_nobf {s : NState} {m : MessageM} (h : ¬ PreBF m s) (pvs : GMap w64 Progress) :
    preState s m pvs = s := by
  simp only [preState, h, ↓reduceIte]

/-- No step-down: a message of no higher term ... -/
theorem PreBF.of_le {m : MessageM} {s : NState} (h : uint.Z m.Term' ≤ uint.Z s.term) : ¬ PreBF m s :=
  fun h' => by have := h'.1; omega

/-- ... a local one ... -/
theorem PreBF.of_zero {m : MessageM} {s : NState} (h : m.Term' = W64 0) : ¬ PreBF m s :=
  fun h' => by
    have h1 := h'.1
    have h2 : uint.Z m.Term' = 0 := by rw [h]; rfl
    have := uint_Z_nonneg s.term
    omega

/-- ... a pre-vote request ... -/
theorem PreBF.of_prevote {m : MessageM} {s : NState} (h : m.Type' = MsgPreVote) : ¬ PreBF m s :=
  fun h' => h'.2.1 h

/-- ... a granted pre-vote response. -/
theorem PreBF.of_prevoteresp {m : MessageM} {s : NState} (h : m.Type' = MsgPreVoteResp)
    (hr : m.Reject' = false) : ¬ PreBF m s :=
  fun h' => h'.2.2 ⟨h, hr⟩

/-- A step-down: a message of a higher term but those. -/
theorem PreBF.of_gt {m : MessageM} {s : NState} (h : uint.Z s.term < uint.Z m.Term')
    (h1 : m.Type' ≠ MsgPreVote) (h2 : m.Type' = MsgPreVoteResp → m.Reject' = true) : PreBF m s :=
  ⟨h, h1, fun ⟨a, b⟩ => by rw [h2 a] at b; cases b⟩

/-- The step-down's leader: a leader's message's sender ... -/
theorem preLead_from {m : MessageM} (h : m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨ m.Type' = MsgSnap) :
    preLead m = m.From' := by
  simp only [preLead, h, ↓reduceIte]

/-- ... else none. -/
theorem preLead_none {m : MessageM} (h1 : m.Type' ≠ MsgApp) (h2 : m.Type' ≠ MsgHeartbeat)
    (h3 : m.Type' ≠ MsgSnap) : preLead m = W64 0 := by
  have h : ¬ (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨ m.Type' = MsgSnap) := by
    rintro (h | h | h) <;> contradiction
  simp only [preLead, h, ↓reduceIte]

theorem preState_bf' {s : NState} {m : MessageM} {lead : w64} (h : PreBF m s) (hl : preLead m = lead)
    (pvs : GMap w64 Progress) :
    preState s m pvs = { becomeFollower s m.Term' lead with prvals := pvs } := by
  rw [preState_bf h, hl]

end pure

section gated
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The receive hook at `Step`'s entry**, gated: the caller's gate at the receipt's event
(`recvGate`), the message as `Step` holds it. -/
abbrev traceReceiveMessage.gatedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dqe : DFrac) (ms : MsgSt) (Q : IProp GF),
  (s.gh.tr ≠ none → mtypeOf ms.msg.Type' ≠ some .snap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      msgIn ml dqe ms ∗ HookGateOpt s.gh.tr r (recvGate id s c ms) Q }}
    (App (App (Val #(functions traceReceiveMessage [])) (Val #r)) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ msgIn ml dqe ms ∗ Q }}

/-- `traceReceiveMessage.gatedTriple` from `traceReceiveMessage.spec` (as
`traceReceiveMessage.tracedSpec_of_spec`). -/
theorem traceReceiveMessage.gated (h : traceReceiveMessage.spec (GF := GF) (hG := hG)) :
    traceReceiveMessage.gatedTriple (GF := GF) (hG := hG) := by
  intro c r id s ml dqe ms Q Hns
  iintro %Φ ⟨#Hpkg, Hphys, Hm, Hg⟩ HΦ
  iunfold HookGateOpt at Hg
  imod Hg with ⟨%tl, #Htl, %Hok, Hfire⟩
  revert Hns Hok
  cases htr : s.gh.tr with
  | none =>
    intro _ Hok
    iapply h r ml tl none (recvGate id s c ms) Q iprop(emp) $$ [$Hpkg $Htl $Hfire]
    · isplitr
      · ipureintro; exact Hok
      iapply trOwn_none_intro
    inext
    iintro ⟨-, HQ⟩
    iapply HΦ
    iframe Hphys Hm HQ
  | some γd =>
    intro Hns Hok
    iapply h r ml tl (some γd) (recvGate id s c ms) Q
      iprop(ownRaftPhysCV c c.voters r id s ∗ msgIn ml dqe ms) $$ [$Hpkg $Htl Hphys Hm $Hfire]
    · isplitr
      · ipureintro; exact Hok
      iapply (trOwn_some γd _).2
      iexists c, id, s, iprop(ownRaftPhysCV c c.voters r id s ∗ msgIn ml dqe ms),
        ⟨DFrac.own 1, dqe, needsCap ms.msg, ms⟩
      iframe Hphys Hm
      isplitr
      · iapply raftLend_sep
      isplitr
      · iapply msgLend_sep_some iprop(ownRaftPhysCV c c.voters r id s) ml
          ⟨DFrac.own 1, dqe, needsCap ms.msg, ms⟩
      isplitr
      · ipureintro; exact ⟨Hns (by simp), rfl⟩
      iintro H; iexact H
    inext
    iintro ⟨Hown, HQ⟩
    iapply HΦ
    iframe HQ
    iapply (trOwn_some γd _).1
    iexact Hown

/-! ### What `Step` gives back -/

theorem stepOut_G0 (R : StepG GF) : R.G0 ⊢ stepOut R := by
  iintro H; unfold stepOut; ileft; iexact H

theorem stepOut_G1 (R : StepG GF) : R.G1 ⊢ stepOut R := by
  iintro H; unfold stepOut; iright; ileft; iexact H

theorem stepOut_GE (R : StepG GF) : R.GE ⊢ stepOut R := by
  iintro H; unfold stepOut; iright; iright; ileft; iexact H

theorem stepOut_Gp2 (R : StepG GF) : R.Gp2 ⊢ stepOut R := by
  iintro H; unfold stepOut; iright; iright; iright; ileft; iexact H

theorem stepOut_Gc (R : StepG GF) (b : Bool) (N : w64) : R.Gc b N ⊢ stepOut R := by
  iintro H; unfold stepOut; iright; iright; iright; iright; iexists b, N; iexact H

/-- A step function's result (`stepFollower`'s, `stepCandidate`'s: `G'` or `G`, tagged). -/
theorem stepOut_or (R : StepG GF) (φ ψ : Prop) :
    iprop((⌜φ⌝ ∗ R.GE) ∨ (⌜ψ⌝ ∗ R.G1)) ⊢ stepOut R := by
  iintro (⟨-, H⟩ | ⟨-, H⟩)
  · iapply stepOut_GE; iexact H
  · iapply stepOut_G1; iexact H

/-- `stepLeader`'s result. -/
theorem stepOut_leader (R : StepG GF) (φ1 φ2 φ4 : Prop) (φ3 : Bool → w64 → Prop) :
    iprop((⌜φ1⌝ ∗ R.GE) ∨ (⌜φ2⌝ ∗ R.Gp2) ∨ (∃ (b : Bool) (N : w64), ⌜φ3 b N⌝ ∗ R.Gc b N) ∨
      (⌜φ4⌝ ∗ R.G1)) ⊢ stepOut R := by
  iintro (⟨-, H⟩ | ⟨-, H⟩ | ⟨%b, %N, -, H⟩ | ⟨-, H⟩)
  · iapply stepOut_GE; iexact H
  · iapply stepOut_Gp2; iexact H
  · iapply stepOut_Gc R b N; iexact H
  · iapply stepOut_G1; iexact H

/-- `hup`'s result. -/
theorem stepOut_hup (R : StepG GF) (φ : Prop) :
    iprop((⌜φ⌝ ∗ R.G1) ∨ R.GE) ⊢ stepOut R := by
  iintro (⟨-, H⟩ | H)
  · iapply stepOut_G1; iexact H
  · iapply stepOut_GE; iexact H

/-- The preamble's gate when it steps down. -/
theorem preGate_bf (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (G0 G1 : IProp GF)
    (lead : w64) (hb : PreBF m s) (hl : preLead m = lead) :
    ⊢ preGate c r id s m G0 G1 -∗ G0 -∗
      HookGate s.gh.tr r (NodeEvOf (W64 2) id (becomeFollower s m.Term' lead) c) G1 := by
  iintro H HG
  unfold preGate
  ihave H := H $$ %(Or.inr (Int.le_of_lt hb.1)) HG
  simp only [hb, ↓reduceIte]; rw [hl]
  iexact H

/-- ... and when it does not (a message not stale). -/
theorem preGate_nobf (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (G0 G1 : IProp GF)
    (hc : m.Term' = W64 0 ∨ uint.Z s.term ≤ uint.Z m.Term') (hn : ¬ PreBF m s) :
    ⊢ preGate c r id s m G0 G1 -∗ G0 -∗ |={⊤}=> G1 := by
  iintro H HG
  unfold preGate
  ihave H := H $$ %hc HG
  simp only [hn, ↓reduceIte]
  iexact H

/-- The step function's gates at the state after the preamble: a follower's ... -/
theorem stepFnGates_follower (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (ctx : List w8) (R : StepG GF) (pvs : GMap w64 Progress) (s1 : NState)
    (hs : preState s m pvs = s1) (hr : s1.role = .follower) :
    stepFnGates c r id s m ents ctx R ⊢ followerGates c r id s1 m ents ctx R.G1 R.GE := by
  iintro H
  unfold stepFnGates
  ispecialize H $$ %pvs
  icases H with ⟨H, -⟩
  rw [hs]
  iapply H; ipureintro; exact hr

/-- ... a (pre-)candidate's ... -/
theorem stepFnGates_candidate (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (ctx : List w8) (R : StepG GF) (pvs : GMap w64 Progress) (s1 : NState)
    (hs : preState s m pvs = s1) (hr : s1.role = .candidate ∨ s1.role = .preCandidate) :
    stepFnGates c r id s m ents ctx R ⊢
      candidateGates c r id s1 m ents ctx R.G1 R.GE R.Gf R.Gb1 R.Gb2 := by
  iintro H
  unfold stepFnGates
  ispecialize H $$ %pvs
  icases H with ⟨-, H, -⟩
  rw [hs]
  iapply H; ipureintro; exact hr

/-- ... a leader's. -/
theorem stepFnGates_leader (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (ctx : List w8) (R : StepG GF) (pvs : GMap w64 Progress) (s1 : NState)
    (hs : preState s m pvs = s1) (hr : s1.role = .leader) :
    stepFnGates c r id s m ents ctx R ⊢ leaderGates c r id s1 m ents R.G1 R.GE R.Gp1 R.Gp2 R.Gc := by
  iintro H
  unfold stepFnGates
  ispecialize H $$ %pvs
  icases H with ⟨-, -, H⟩
  rw [hs]
  iapply H; ipureintro; exact hr

/-- `hup`'s gates at the campaign `Step` starts. -/
theorem hupGates_type (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType) (G0 G : IProp GF)
    (h : hupType s = t) : hupGates c r id s (hupType s) G0 G ⊢ hupGates c r id s t G0 G := by
  rw [h]

omit [GooseSemantics] [GooseInterp] [StorageModel GF] in
theorem hupType_pre {s : NState} (h : s.prevote = true) : hupType s = go!"CampaignPreElection" := by
  simp [hupType, h, campaignPreElection]

omit [GooseSemantics] [GooseInterp] [StorageModel GF] in
theorem hupType_el {s : NState} (h : s.prevote = false) : hupType s = go!"CampaignElection" := by
  simp [hupType, h, campaignElection]

/-- A pre-vote response is not traced. -/
theorem sendOutGate_preVoteResp (id : w64) (s : NState) (c : CfgM) (out : List Msg) :
    sendOutGate id s c MsgPreVoteResp out = none := by
  simp [sendOutGate, mtypeOf_MsgPreVoteResp, sendEvt]

/-- A vote request's answer through `Step`'s gate (`"Hgvresp"`), at the state `s1` after the
preamble: a `MsgVote`'s ... -/
theorem vrespGate_vote (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (R : StepG GF)
    (pvs : GMap w64 Progress) (s1 : NState) (hs : preState s m pvs = s1) (hty : m.Type' = MsgVote)
    (rej : Bool) (T : w64) (hT : T = if rej then s1.term else m.Term') :
    ⊢ (∀ (pvs : GMap w64 Progress) (rej : Bool),
        R.G1 -∗ HookGateOpt s.gh.tr r
          (sendOutGate id (preState s m pvs) c (vrespTyOf m) [vrespMsgOf id (preState s m pvs) m rej]) R.GE) -∗
      R.G1 -∗ HookGateOpt s1.gh.tr r (sendOutGate id s1 c MsgVoteResp [Msg.plain .voteResp id m.From' T rej])
        R.GE := by
  iintro H HG
  ihave H := H $$ %pvs %rej HG
  have hgh : s1.gh = s.gh := by rw [← hs, preState_gh]
  rw [hs, hgh, hT]
  simp only [vrespTyOf, vrespMsgOf, hty, ↓reduceIte]
  iexact H

/-- ... a `MsgPreVote`'s (at no event). -/
theorem vrespGate_prevote (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (R : StepG GF)
    (pvs : GMap w64 Progress) (s1 : NState) (hs : preState s m pvs = s1) (hty : m.Type' = MsgPreVote)
    (out : List Msg) :
    ⊢ (∀ (pvs : GMap w64 Progress) (rej : Bool),
        R.G1 -∗ HookGateOpt s.gh.tr r
          (sendOutGate id (preState s m pvs) c (vrespTyOf m) [vrespMsgOf id (preState s m pvs) m rej]) R.GE) -∗
      R.G1 -∗ HookGateOpt s1.gh.tr r (sendOutGate id s1 c MsgPreVoteResp out) R.GE := by
  iintro H HG
  ihave H := H $$ %pvs %false HG
  have hgh : s1.gh = s.gh := by rw [← hs, preState_gh]
  have hne : m.Type' ≠ MsgVote := by rw [hty]; exact of_decide_eq_true rfl
  rw [hs, hgh]
  simp only [vrespTyOf, hne, ↓reduceIte, sendOutGate_preVoteResp]
  iexact H

/-- A stale pre-vote request's rejection through `Step`'s gate (`"Hglow"`, at no event). -/
theorem lowGate_prevote (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (R : StepG GF)
    (hty : m.Type' = MsgPreVote) (out : List Msg) :
    ⊢ (∀ (ty : w32) (mm : Msg),
        ⌜LowSend id s m ty mm⌝ -∗ R.G0 -∗ HookGateOpt s.gh.tr r (sendOutGate id s c ty [mm]) R.GE) -∗
      R.G0 -∗ HookGateOpt s.gh.tr r (sendOutGate id s c MsgPreVoteResp out) R.GE := by
  iintro H HG
  ihave H := H $$ %MsgPreVoteResp %(Msg.plain .preVoteResp id m.From' s.term true)
    %(.inr ⟨rfl, hty, rfl⟩) HG
  rw [sendOutGate_preVoteResp] at *
  rw [sendOutGate_preVoteResp]
  iexact H

/-- An `if` of resources, at its condition. -/
theorem ite_pos_entails {p : Prop} [Decidable p] (h : p) (A B : IProp GF) :
    (if p then A else B) ⊢ A := by
  split
  · exact .rfl
  · contradiction

theorem ite_neg_entails {p : Prop} [Decidable p] (h : ¬ p) (A B : IProp GF) :
    (if p then A else B) ⊢ B := by
  split
  · contradiction
  · exact .rfl

/-! ### Raft's ghost state through the gates (`raft.Step`'s proof) -/

section ghostgate
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
  [go_etcd_io.raft.v3.Assumptions]

/-- The ghost state into the caller's first resource (the receive hook's gate's argument). -/
theorem gate_open (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) (R : StepG GF) :
    ⊢ ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗ R.G -∗
      (ghostIn γ md c id s R).G := by
  iintro Hg Hr HG
  unfold ghostIn ownStepGhost
  dsimp only
  iframe

/-- ... and back, with the caller's `Gout` and the outbox's numbers. -/
theorem gate_close (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM) (s : NState)
    (R : StepG GF) (Gout : IProp GF) (s' : NState) (B : Int) (recv : List Msg)
    (h : s.gh.tr.isSome → StepCD c id B m s recv s') :
    ⊢ stepClose γ md c id m s R Gout -∗
      stepOut (ghostIn γ md c id s R) -∗
      |={⊤}=> ownRaftGhost γ id (toPState s) md.isDyn ∗ ghostRest γ md c id s ∗ Gout ∗
        ⌜OutTrStep s s'⌝ := by
  iintro Hc Ho
  have hw : stepOut (ghostIn γ md c id s R) ⊢ stepOut R := .rfl
  ihave Ho := hw $$ Ho
  unfold stepClose
  imod Hc $$ %s' %B %recv %h Ho with ⟨Hg, HG, %Hot⟩
  unfold ownStepGhost
  icases Hg with ⟨Hg, Hr⟩
  imodintro
  iframe Hg Hr HG
  ipureintro; exact Hot

end ghostgate

/-! ### A transfer request's gates at the state with the forward recorded (`NGhost.xw`) -/

theorem preState_role_follower {s : NState} {m : MessageM} (h : s.role = .follower)
    (pvs : GMap w64 Progress) : (preState s m pvs).role = .follower := by
  unfold preState; split
  · rfl
  · exact h

set_option hygiene false in
/-- A transfer request is none of the other types the gates are premised on. -/
local macro "tl_ne" : tactic => `(tactic| (
  intro h
  rw [hty] at h
  revert h
  simp only [MsgTransferLeader, MsgVote, MsgPreVote, MsgHup, MsgApp, MsgHeartbeat, MsgTimeoutNow,
    MsgProp, MsgReadIndex]
  intro h
  exact absurd h (of_decide_eq_true rfl)))

/-- **`Step`'s gates for a leader-transfer request at a follower, at the state with the forward
recorded** (`raft.Step`'s transfer arm records the node's leader in `NGhost.xw` before the step): the
gates such a request runs read nothing of `xw`; the others are refuted by the type or the role. -/
theorem stepGates_xw (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (R : StepG GF) (X : GSet (w64 × w64))
    (hty : m.Type' = MsgTransferLeader) (hrole : s.role = .follower) :
    stepGates c r id s m ents sn ctx rs R ⊢
      stepGates c r id { s with gh := { s.gh with xw := X } } m ents sn ctx rs R := by
  have e1 : recvGate id ({ s with gh := { s.gh with xw := X } } : NState) c ⟨m, ents, sn, ctx, rs⟩ =
      recvGate id s c ⟨m, ents, sn, ctx, rs⟩ := rfl
  have e2 : preGate (GF := GF) c r id ({ s with gh := { s.gh with xw := X } } : NState) m R.G0 R.G1 =
      preGate c r id s m R.G0 R.G1 := rfl
  have e3 : ∀ ty mm, LowSend id ({ s with gh := { s.gh with xw := X } } : NState) m ty mm =
      LowSend id s m ty mm := fun _ _ => rfl
  have e4 : ∀ ty mm, sendOutGate id ({ s with gh := { s.gh with xw := X } } : NState) c ty [mm] =
      sendOutGate id s c ty [mm] := fun _ _ => rfl
  iintro H
  unfold stepGates
  icases H with ⟨Hgrecv, Hgpre, Hglow, -, -, Hgstep⟩
  isplitl [Hgrecv]
  · rw [e1]; iexact Hgrecv
  isplitl [Hgpre]
  · rw [e2]; iexact Hgpre
  isplitl [Hglow]
  · simp only [e3, e4]; iexact Hglow
  isplitr
  · iintro %h; exfalso; rcases h with h | h <;> revert h <;> tl_ne
  isplitr
  · iintro %h; exfalso; revert h; tl_ne
  unfold stepFnGates
  iintro %pvs
  ispecialize Hgstep $$ %pvs
  isplit
  · icases Hgstep with ⟨Hf, -⟩
    iintro %_
    ihave Hf := Hf $$ %(preState_role_follower hrole pvs)
    unfold followerGates
    icases Hf with ⟨-, -, Hgfwd, -, -⟩
    isplitr
    · iintro %h; exfalso; revert h; tl_ne
    isplitr
    · iintro %h; exfalso; revert h; tl_ne
    isplitl [Hgfwd]
    · rw [preState_gh, preState_gh]
      iexact Hgfwd
    isplitr
    · iintro %h; exfalso; revert h; tl_ne
    · imodintro; iintro %h; exfalso; revert h; tl_ne
  isplit
  · iintro %h; exfalso
    rw [preState_role_follower (s := { s with gh := { s.gh with xw := X } }) hrole pvs] at h
    rcases h with h | h <;> cases h
  · iintro %h; exfalso
    rw [preState_role_follower (s := { s with gh := { s.gh with xw := X } }) hrole pvs] at h
    cases h

/-! ### The gates of an untraced node -/

/-- `stepOut` at one resource. -/
theorem stepOut_const (G X : IProp GF) :
    stepOut ⟨G, X, X, X, X, X, X, X, X, fun _ _ => X⟩ ⊢ X := by
  unfold stepOut
  iintro (H | H | H | H | ⟨%b, %N, H⟩) <;> iexact H

theorem hupGates_none (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType)
    (tl : GoInterface) (X : IProp GF) (htr : s.gh.tr = none) (Htlok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢ hupGates c r id s t X X := by
  iintro #Htl
  unfold hupGates
  rw [htr]
  isplitl
  · iintro HX
    split
    · imodintro; iexact HX
    · iapply hookGate_none r _ tl X Htlok
      iframe Htl HX
  · imodintro
    iintro %pvs %y %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX

theorem followerGates_none (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (cl : List w8) (tl : GoInterface) (X : IProp GF) (htr : s.gh.tr = none)
    (Htlok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢ followerGates c r id s m ents cl X X := by
  iintro #Htl
  unfold followerGates
  rw [htr]
  isplitr
  · iintro %_ %s1 %mm %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ HX
    iapply hookGate_none r _ tl X Htlok
    iframe Htl HX
  · imodintro
    iintro %_ %pvs %y %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX

theorem candidateGates_none (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (cl : List w8) (tl : GoInterface) (X : IProp GF) (htr : s.gh.tr = none)
    (Htlok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢ candidateGates c r id s m ents cl X X X X X := by
  iintro #Htl
  unfold candidateGates
  rw [htr]
  isplitr
  · iintro %_ HX
    iapply hookGate_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %pvs %s1 %mm %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %pvs HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ HX
    iapply hookGate_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro HX
    iapply hookGateN_none r _ 1 tl X Htlok
    iframe Htl HX
  isplitr
  · iintro HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · imodintro
    iintro %_ %pvs %to %mm %_ %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iapply trNoSnap_none
  isplitr
  · iintro %_ HX
    iapply hookGate_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · imodintro
    iintro %_ %pvs %y %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  · iintro %_ HX
    iapply hookGate_none r _ tl X Htlok
    iframe Htl HX

theorem leaderGates_none (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (tl : GoInterface) (X : IProp GF) (htr : s.gh.tr = none)
    (Htlok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢
      leaderGates c r id s m ents X X X X (fun _ _ => X) := by
  iintro #Htl
  unfold leaderGates
  rw [htr]
  isplitr
  · imodintro
    iintro %_ %to %cm %_ %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · imodintro
    iintro %_ %_ %to %cm %_ %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %mm %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iapply trNoSnap_none
  isplitr
  · iintro %_ HX
    iapply hookGate_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %cs _ HX
    iapply hookGateN_none r _ _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %cs _ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · imodintro
    iintro %_ %cs %to %mm _ %_ %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %mm %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · imodintro
    iintro %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %pvs %b %N %_ %_ HX
    iapply hookGate_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · imodintro
    iintro %_ %N %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · imodintro
    iintro %_ %_ %N %k %to %cm %_ %_ %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · imodintro
    iintro %_ %b %N %to %mm %_ %_ HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  · imodintro
    iintro %_ %b %N HX
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX

/-- **`Step`'s gates at an untraced node**: every resource after the receive hook one `X`, which the
caller's first one `G` gives. -/
theorem stepGates_none (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (tl : GoInterface) (G X : IProp GF) (hGX : G ⊢ X) (htr : s.gh.tr = none)
    (Htlok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢
      stepGates c r id s m ents sn ctx rs ⟨G, X, X, X, X, X, X, X, X, fun _ _ => X⟩ := by
  iintro #Htl
  have hgh : ∀ pvs, (preState s m pvs).gh.tr = none := fun pvs => by rw [preState_gh]; exact htr
  unfold stepGates
  isplitr
  · iintro HG
    ihave HX := hGX $$ HG
    rw [htr]
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · unfold preGate
    iintro %_ HX
    split
    · rw [htr]
      iapply hookGate_none r _ tl X Htlok
      iframe Htl HX
    · imodintro; iexact HX
  isplitr
  · iintro %_ %ty %mm %_ HX
    rw [htr]
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_ %pvs %rej HX
    rw [htr]
    iapply hookGateOpt_none r _ tl X Htlok
    iframe Htl HX
  isplitr
  · iintro %_
    iapply hupGates_none c r id s (hupType s) tl X htr Htlok
    iexact Htl
  unfold stepFnGates
  iintro %pvs
  isplit
  · iintro %_
    iapply followerGates_none c r id (preState s m pvs) m ents ctx tl X (hgh pvs) Htlok
    iexact Htl
  isplit
  · iintro %_
    iapply candidateGates_none c r id (preState s m pvs) m ents ctx tl X (hgh pvs) Htlok
    iexact Htl
  · iintro %_
    iapply leaderGates_none c r id (preState s m pvs) m ents tl X (hgh pvs) Htlok
    iexact Htl

end gated

end EtcdGrove
end Perennial
