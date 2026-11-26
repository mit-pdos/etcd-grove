/-
Lean-first (no Rocq counterpart).

# The Sim's proof mask (#33 parity B1)

The statements (`Stmts.lean`) are over every run `R` and every input. Their proofs come in batches
(`~/coordinator-notes/plans/antithesis-parity-plan.md` §3): each batch proves the statements for
the runs and inputs a mask admits, and the next batch widens the mask by proving the new cases,
never restating. A `SimMask` is that mask: the RawNode features (`RnMode`), the node flags
(`NodeK`), the inputs outside both (`Campaign`, `ReportUnreachable`) and the driver's modes (batch,
parallel, split, restarts). `InMask msk R net xnet` says the run and what it sent are within `msk`;
`ReachIn msk`/`QuietIn msk` are `Reach`/`Quiet` with the input admitted by `msk`
(`Input.InMask`). Each migrated statement is `antSim_X_in msk (hmsk : msk ≤ mskB1)` (parity B1); later batches widen it,
and at `mskTop` it gives the plain `antSim_X : antSim_X.stmt` (`ReachIn.ofReach_top`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShapeStmt

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

/-- `a` admits no more than `b`. -/
def BLe (a b : Bool) : Prop := a = true → b = true

/-- The RawNode features of `a` are among `b`'s. -/
def RnMode.Le (a b : RnMode) : Prop :=
  BLe a.prevote b.prevote ∧ BLe a.cq b.cq ∧ BLe a.reads b.reads ∧ BLe a.transfer b.transfer ∧
  BLe a.forwarding b.forwarding ∧ BLe a.snapshots b.snapshots ∧ BLe a.confChanges b.confChanges ∧
  BLe a.async b.async ∧ BLe a.nonVoters b.nonVoters

/-- The node flags of `a` are among `b`'s. -/
def NodeK.Le (a b : NodeK) : Prop := BLe a.prevote b.prevote ∧ BLe a.cq b.cq ∧ BLe a.sdr b.sdr

/-- **A proof batch's mask**: the RawNode features, node flags, inputs and driver modes its proofs
cover. -/
structure SimMask where
  md : RnMode := {}
  k : NodeK := {}
  campaign : Bool := false
  unreachable : Bool := false
  batch : Bool := false
  parallel : Bool := false
  split : Bool := false
  restarts : Bool := false

/-- `a` admits no more than `b`. -/
def SimMask.Le (a b : SimMask) : Prop :=
  RnMode.Le a.md b.md ∧ NodeK.Le a.k b.k ∧ BLe a.campaign b.campaign ∧
  BLe a.unreachable b.unreachable ∧ BLe a.batch b.batch ∧ BLe a.parallel b.parallel ∧
  BLe a.split b.split ∧ BLe a.restarts b.restarts

instance : LE SimMask := ⟨SimMask.Le⟩

/-- The first harness's scope (S4): sync storage, no feature, recv/tick/propose only. -/
def mskS4 : SimMask := {}

/-- **Parity B1's scope**: `mskS4` with `Campaign`, `ReportUnreachable`, non-voters (servers outside
the initial configuration, `R.K < R.N`), pre-vote, check quorum (features and node flags), each
node's `StepDownOnRemoval`, reads and transfer; sync storage, no snapshot, no conf change, no driver
mode. B1's other run freedoms need no mask field, as no statement reads them: duplication
(`R.drv.maxDeliveries`: a message received stays on the network, so it can be received again), the
limits (`MaxInflightMsgs`, `MaxSizePerMsg`: the relations admit any `SendOk` sends) and
bootstrapping (`R.boot`: every statement is over every `R`). -/
def mskB1 : SimMask :=
  { md := { prevote := true, cq := true, reads := true, transfer := true, nonVoters := true },
    k := { prevote := true, cq := true, sdr := true }, campaign := true, unreachable := true }

/-- Everything: the plain statements. -/
def mskTop : SimMask :=
  { md := { prevote := true, cq := true, reads := true, transfer := true, forwarding := true,
            snapshots := true, confChanges := true, async := true, nonVoters := true },
    k := { prevote := true, cq := true, sdr := true }, campaign := true, unreachable := true,
    batch := true, parallel := true, split := true, restarts := true }

section inputs
variable [GooseExts]

/-- **The run and what it sent are within the mask**: its features, every node's flags and the
driver's modes are the mask's; every message sent is of a type the mask's network carries (or a
forwarded proposal), and transfer messages only with transfers. -/
def InMask (msk : SimMask) (R : RunCfg) (net : List Msg) (xnet : List XMsg) : Prop :=
  RnMode.Le R.md msk.md ∧ (∀ n, NodeK.Le (R.k n) msk.k) ∧ BLe R.drv.batch msk.batch ∧
  BLe R.drv.parallel msk.parallel ∧ (R.drv.split ≠ 0 → msk.split = true) ∧
  BLe R.drv.restarts msk.restarts ∧ (∀ m ∈ net, NetTy msk.md m.ty ∨ m.ty = MsgType.propose) ∧
  (msk.md.transfer = false → xnet = [])


/-- **The inputs the mask admits.** -/
def Input.InMask (msk : SimMask) : Input → Prop
  | .recv _ | .tick | .propose _ => True
  | .recvX _ | .transfer _ => msk.md.transfer = true
  | .proposeConf _ _ | .applyConf _ => msk.md.confChanges = true
  | .readIndex _ => msk.md.reads = true
  | .campaign => msk.campaign = true
  | .snapStatus _ _ => msk.md.snapshots = true
  | .unreachable _ => msk.unreachable = true
  | .storeAck _ => msk.md.async = true

/-- `Reach` with the input admitted by the mask. -/
inductive ReachIn (msk : SimMask) (R : RunCfg) (dec : CCDec) (Adm : List EntryM → CCState → Prop)
    (net : List Msg) (xnet : List XMsg) (n : Fin R.N) : NodeView → RState → Prop
  | stay (v : NodeView) : v.Idle → DrainBy v.byE → ReachIn msk R dec Adm net xnet n v v.r
  | input (v : NodeView) (inp : Input) (r₁ : RState) :
      inp.InMask msk →
      v.Idle → v.byE = inp.byE → v.cause = inp.cause → v.xcause = inp.xcause →
      (∀ m, inp = .recv m → m ∈ net ∧ m.dst = nodeId n ∧ (m.ty ≠ .readIndex → m.term ≠ W64 0)) →
      (∀ x, inp = .recvX x → x ∈ xnet ∧ x.dst = nodeId n) →
      InputStep R dec Adm n v.r inp r₁ → ReachIn msk R dec Adm net xnet n v r₁
  | advance (v : NodeView) (r₁ : RState) :
      v.pend = [] → v.xpend = [] → v.ce = [] → v.rpend = [] → DrainBy v.byE →
      AdvanceEndR Adm dec (R.k n) (nodeId n) v.r v.qs r₁ →
      (R.md.snapshots = false → AdvanceNoSnap Adm dec (R.k n) (nodeId n) v.r v.qs r₁) →
      ReachIn msk R dec Adm net xnet n v r₁

/-- `Quiet` with the input admitted by the mask. -/
inductive QuietIn (msk : SimMask) (R : RunCfg) (dec : CCDec) (Adm : List EntryM → CCState → Prop)
    (net : List Msg) (xnet : List XMsg) (n : Fin R.N) : NodeView → NodeView → Prop
  | input (v : NodeView) (inp : Input) :
      inp.InMask msk →
      v.Idle → (∀ m, inp = .recv m → m ∈ net ∧ m.dst = nodeId n) →
      (∀ x, inp = .recvX x → x ∈ xnet ∧ x.dst = nodeId n) →
      QuietIn msk R dec Adm net xnet n v (v.noteInput inp)
  | noReady (v : NodeView) (r₁ : RState) :
      ReachIn msk R dec Adm net xnet n v r₁ → r₁.p.outbox = [] → r₁.p.rd.states = [] →
      r₁.p.term = v.ps.term → r₁.p.vote = v.ps.vote → r₁.p.commit = v.ps.commit →
      r₁.p.role = v.ps.role → r₁.full = v.r.full →
      QuietIn msk R dec Adm net xnet n v { v with r := r₁, qs := [] }
  | silentReady (v : NodeView) (r₁ : RState) (rd : ReadyD) :
      ReachIn msk R dec Adm net xnet n v r₁ → ReadyOutP R n v r₁ rd → ¬ Reported v rd →
      QuietIn msk R dec Adm net xnet n v (v.drainOf r₁ rd)

theorem ReachIn.reach {msk : SimMask} {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : NodeView} {r₁ : RState}
    (h : ReachIn msk R dec Adm net xnet n v r₁) : Reach R dec Adm net xnet n v r₁ := by
  cases h with
  | stay h1 h2 => exact .stay _ h1 h2
  | input inp _ h0 h1 h2 h3 h4 h5 h6 h7 => exact .input _ inp _ h1 h2 h3 h4 h5 h6 h7
  | advance _ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

theorem Input.inMask_top [GooseExts] (inp : Input) : inp.InMask mskTop := by
  cases inp <;> simp [Input.InMask, mskTop]

theorem ReachIn.ofReach_top {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : NodeView} {r₁ : RState}
    (h : Reach R dec Adm net xnet n v r₁) : ReachIn mskTop R dec Adm net xnet n v r₁ := by
  cases h with
  | stay h1 h2 => exact .stay _ h1 h2
  | input inp _ h1 h2 h3 h4 h5 h6 h7 => exact .input _ inp _ (Input.inMask_top inp) h1 h2 h3 h4 h5 h6 h7
  | advance _ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

theorem QuietIn.ofQuiet_top {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v v' : NodeView}
    (h : Quiet R dec Adm net xnet n v v') : QuietIn mskTop R dec Adm net xnet n v v' := by
  cases h with
  | input inp h1 h2 h3 => exact .input _ inp (Input.inMask_top inp) h1 h2 h3
  | noReady _ h1 h2 h3 h4 h5 h6 h7 h8 => exact .noReady _ _ (ReachIn.ofReach_top h1) h2 h3 h4 h5 h6 h7 h8
  | silentReady _ _ h1 h2 h3 => exact .silentReady _ _ _ (ReachIn.ofReach_top h1) h2 h3

/-! ## Parity B1: pre-vote, check quorum, reads, transfer and `ReportUnreachable` (`mskB1`)

`mskS4` with `Campaign`, `ReportUnreachable`, non-voters, pre-vote and check quorum on (RawNode
features and node flags), each node's `StepDownOnRemoval`, reads (`ReadIndex` inputs, read requests
forwarded and answered, heartbeats with read contexts, deferred requests released) and transfer
(`TransferLeader` inputs, `MsgTransferLeader`/`MsgTimeoutNow` received). The per-input end relations
are read on the protocol state (`ReachP`): `InputEnd.lean`'s `RecvEnd`, `TickEnd` and `AdvanceEnd`
at the node's configuration, a pre-candidate's self pre-votes (`advanceEnd_pre`) and the transfer
arms. -/

/-- `RawNode.Campaign` is a tick's campaign or pre-campaign step (whatever the node's pre-vote). -/
theorem tickEndR_of_campaignEndR' {k : NodeK} {id : w64} {r r' : RState}
    (h : CampaignEndR k id r r') : TickEndR k id r r' := by
  obtain ⟨h0 | ⟨hnl, -, -, ⟨hk, hce⟩ | ⟨hk', hpc⟩⟩, hkc, hfp, hsn, hpci⟩ := h
  · subst h0; exact ⟨.inl rfl, hkc, hfp, hsn, hpci⟩
  · exact ⟨.inr (.inl ⟨hnl, hk, hce⟩), hkc, hfp, hsn, hpci⟩
  · exact ⟨.inr (.inr (.inl ⟨hnl, hk', hpc⟩)), hkc, hfp, hsn, hpci⟩

/-- Below `mskB1`, the mask admits only recv, tick, propose, campaign, read requests, the transfer
inputs and `ReportUnreachable`. -/
theorem Input.inMask_b1 {msk : SimMask} (hmsk : msk ≤ mskB1) {inp : Input} (h : inp.InMask msk) :
    (∃ m, inp = .recv m) ∨ inp = .tick ∨ (∃ d, inp = .propose d) ∨ inp = .campaign ∨
      (∃ c, inp = .readIndex c) ∨ (∃ x, inp = .recvX x) ∨ (∃ to, inp = .transfer to) ∨
      ∃ t, inp = .unreachable t := by
  obtain ⟨⟨_, _, _, h4, _, h6, h7, h8, _⟩, _, _, h12, _⟩ := hmsk
  cases inp <;> simp_all [Input.InMask, BLe, mskB1]

/-- The S4 types (and a proposal). -/
def S4Ty (t : MsgType) : Prop :=
  t = .app ∨ t = .appResp ∨ t = .vote ∨ t = .voteResp ∨ t = .heartbeat ∨ t = .heartbeatResp ∨
    t = .propose

/-- The S4 types and the read-index request and response: the types `ReachP.recv` steps (the pre-vote
  types are `ReachP.recvP`'s). -/
def RdTy (t : MsgType) : Prop := S4Ty t ∨ t = .readIndex ∨ t = .readIndexResp

/-- The types of `mskB1`'s network: the readings' and the pre-vote request and response. -/
def B1rTy (t : MsgType) : Prop := RdTy t ∨ t = .preVote ∨ t = .preVoteResp

/-- Below `mskB1`, the run has pre-vote, check quorum, reads, transfer and non-voters at most, no
driver mode, and its network only `B1rTy`. -/
theorem InMask.b1 {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {net : List Msg}
    {xnet : List XMsg} (h : InMask msk R net xnet) :
    R.md = { prevote := R.md.prevote, cq := R.md.cq, reads := R.md.reads, transfer := R.md.transfer,
             nonVoters := R.md.nonVoters } ∧
    R.drv.batch = false ∧ R.drv.parallel = false ∧ R.drv.split = 0 ∧ R.drv.restarts = false ∧
    ∀ m ∈ net, B1rTy m.ty := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, ⟨k1, k2, k3⟩, c1, c2, c3, c4, c5, c6⟩ := hmsk
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩, hk, d1, d2, d3, d4, hnet, hx⟩ := h
  simp only [BLe, mskB1] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hR : R.md; simp_all
  · cases h : R.drv.batch <;> simp_all
  · cases h : R.drv.parallel <;> simp_all
  · cases h : R.drv.split with
    | zero => rfl
    | succ _ => exact absurd (d3 (by simp [h])) (by simp_all)
  · cases h : R.drv.restarts <;> simp_all
  · intro m hm; rcases hnet m hm with h | h
    · simp only [NetTy] at h
      rcases h with h | h | h | h | h | h | ⟨-, h | h⟩ | ⟨-, h | h⟩ | ⟨hp, _⟩ <;>
        simp_all [B1rTy, RdTy, S4Ty]
    · simp [B1rTy, RdTy, S4Ty, h]

/-- **An input below `mskB1`**: a message received, a proposal, a tick's step (a tick, or
`Campaign`: `tickEndR_of_campaignEndR'`), a read request, a transfer message received, a transfer,
or `ReportUnreachable` (nothing changed). -/
theorem Input.step_b1 {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {n : Fin R.N}
    {r r₁ : RState} {inp : Input}
    (h : inp.InMask msk) (hs : InputStep R dec Adm n r inp r₁) :
    (∃ m, inp = .recv m) ∨ ((inp = .tick ∨ inp = .campaign) ∧ InputStep R dec Adm n r .tick r₁) ∨
      (∃ d, inp = .propose d) ∨ (∃ c, inp = .readIndex c) ∨ (∃ x, inp = .recvX x) ∨
      (∃ to, inp = .transfer to) ∨ ((∃ t, inp = .unreachable t) ∧ r₁ = r) := by
  rcases Input.inMask_b1 hmsk h with ⟨m, rfl⟩ | rfl | ⟨d, rfl⟩ | rfl | ⟨c, rfl⟩ | ⟨x, rfl⟩ | ⟨to, rfl⟩ |
      ⟨t, rfl⟩
  · exact .inl ⟨m, rfl⟩
  · exact .inr (.inl ⟨.inl rfl, hs⟩)
  · exact .inr (.inr (.inl ⟨d, rfl⟩))
  · exact .inr (.inl ⟨.inr rfl, tickEndR_of_campaignEndR' hs⟩)
  · exact .inr (.inr (.inr (.inl ⟨c, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨x, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨to, rfl⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨⟨t, rfl⟩, hs⟩)))))

/-- The transfer inputs and `ReportUnreachable` keep the configuration, the ghost prefix and the
restored flag. -/
theorem inputStep_x_keep {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop} {n : Fin R.N}
    {r r₁ : RState} {inp : Input}
    (hx : (∃ x, inp = .recvX x) ∨ (∃ to, inp = .transfer to) ∨ ((∃ t, inp = .unreachable t) ∧ r₁ = r))
    (hs : InputStep R dec Adm n r inp r₁) : r₁.cfg = r.cfg ∧ r₁.fp = r.fp ∧ r₁.snap = r.snap := by
  rcases hx with ⟨x, rfl⟩ | ⟨to, rfl⟩ | ⟨-, rfl⟩
  · rcases hs with ⟨-, ⟨-, rfl⟩ | ⟨-, -, ⟨-, -, hc⟩, hfp, hsn, -⟩⟩ |
        ⟨-, ⟨-, -, rfl⟩ | ⟨-, hT⟩ | ⟨-, rfl⟩⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨hc, hfp, hsn⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨hT.2.2.1, hT.2.2.2.1, hT.2.2.2.2.1⟩
    · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
  · exact ⟨rfl, rfl, rfl⟩

/-! ### The end relations below `mskB1` -/

theorem not_preTy {m : Msg} (hty : RdTy m.ty) :
    ¬ (m.ty = .preVote ∨ (m.ty = .preVoteResp ∧ m.reject = false)) := by
  rintro (h | ⟨h, -⟩) <;> rcases hty with (h' | h' | h' | h' | h' | h' | h') | h' | h' <;>
    rw [h'] at h <;> cases h

/-- `HandleEnd` of a pre-vote response at `s`: nothing, or on a grant at a follower with no leader
the campaign. -/
theorem handleEnd_preVoteResp {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hty : m.ty = .preVoteResp) (h : HandleEnd k c id s m s') :
    s' = s ∨ (s.role = .follower ∧ s.lead = W64 0 ∧ m.reject = false ∧ CampaignSends c id s [] s') := by
  simp only [HandleEnd, hty] at h
  split at h
  · rename_i hfl
    rcases h with h | ⟨hrj, hcs⟩
    · exact .inl h
    · exact .inr ⟨hfl.1, hfl.2, hrj, hcs⟩
  · exact .inl h

/-- **`RecvEnd` of a pre-vote request or response**: nothing; a stale pre-vote request rejected at
the node's term; a pre-vote request answered (`PreVoteEndP`, the term kept); a rejected pre-vote
response of a higher term making a follower with no leader at its term; on a grant at a follower
with no leader, the campaign (`CampaignSends`, the election's requests with no context). -/
theorem recvEnd_pre {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hty : m.ty = .preVote ∨ m.ty = .preVoteResp) (h : RecvEnd k c id s m s') :
    s' = s ∨
    (uint.Z m.term < uint.Z s.term ∧ m.ty = .preVote ∧
      s' = psendMsgs s [Msg.plain .preVoteResp id m.src s.term true]) ∨
    (m.ty = .preVote ∧ PreVoteEndP id s m s') ∨
    (m.ty = .preVoteResp ∧ m.reject = true ∧ uint.Z s.term < uint.Z m.term ∧
      s' = pbecomeFollower s m.term (W64 0)) ∨
    (m.ty = .preVoteResp ∧ s.role = .follower ∧ s.lead = W64 0 ∧ m.reject = false ∧
      CampaignSends c id s [] s') := by
  rcases hty with hpv | hpr
  · have hhd : ∀ {s1 : PState}, HandleEnd k c id s1 m s' → PreVoteEndP id s1 m s' := by
      intro s1 hh; simp only [HandleEnd, hpv] at hh; exact hh
    rcases h with ⟨-, hh⟩ | ⟨-, hlt, hst⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
    · exact .inr (.inr (.inl ⟨hpv, hhd hh⟩))
    · rcases hst with rfl | ⟨-, happ, -⟩ | ⟨-, rfl⟩
      · exact .inl rfl
      · rw [hpv] at happ; rcases happ with h' | h' <;> cases h'
      · exact .inr (.inl ⟨hlt, hpv, rfl⟩)
    · exact .inl rfl
    · rcases hpre with ⟨-, hk, -⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact absurd (.inl hpv) hk
      · exact .inr (.inr (.inl ⟨hpv, hhd hh⟩))
      · exact .inr (.inr (.inl ⟨hpv, hhd hh⟩))
  · have hhr : ∀ {s1 : PState}, HandleEnd k c id s1 m s' → s1 = s →
        s' = s ∨ (s.role = .follower ∧ s.lead = W64 0 ∧ m.reject = false ∧ CampaignSends c id s [] s') := by
      rintro s1 hh rfl; exact handleEnd_preVoteResp hpr hh
    rcases h with ⟨-, hh⟩ | ⟨-, -, hst⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
    · rcases hhr hh rfl with h' | h'
      · exact .inl h'
      · exact .inr (.inr (.inr (.inr ⟨hpr, h'⟩)))
    · rcases hst with rfl | ⟨-, happ, -⟩ | ⟨hpv, -⟩
      · exact .inl rfl
      · rw [hpr] at happ; rcases happ with h' | h' <;> cases h'
      · rw [hpr] at hpv; cases hpv
    · exact .inl rfl
    · rcases hpre with ⟨hlt, hk, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · have hrj : m.reject = true := by
          cases h : m.reject
          · exact absurd (.inr ⟨hpr, h⟩) hk
          · rfl
        have hfl : fromLeader m.ty = false := by rw [hpr]; rfl
        simp only [hfl, Bool.false_eq_true, if_false] at hh
        rcases handleEnd_preVoteResp hpr hh with h' | ⟨-, -, h', -⟩
        · exact .inr (.inr (.inr (.inl ⟨hpr, hrj, hlt, h'⟩)))
        · rw [hrj] at h'; cases h'
      · rcases hhr hh rfl with h' | h'
        · exact .inl h'
        · exact .inr (.inr (.inr (.inr ⟨hpr, h'⟩)))
      · rcases hhr hh rfl with h' | h'
        · exact .inl h'
        · exact .inr (.inr (.inr (.inr ⟨hpr, h'⟩)))

/-- **`RecvEnd` of a self-acknowledgement or a self-vote at the node's term** is the type switch at
the state itself (no stale answer, no lease for these types, no term adopted). -/
theorem recvEnd_self {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hty : m.ty = .appResp ∨ m.ty = .voteResp) (ht : m.term = s.term) (h : RecvEnd k c id s m s') :
    HandleEnd k c id s m s' := by
  rcases h with ⟨-, hh⟩ | ⟨-, hlt, -⟩ | ⟨-, ⟨-, h1 | h1, -⟩, -⟩ | ⟨-, s1, hpre, hh⟩
  · exact hh
  · rw [ht] at hlt; exact absurd hlt (Int.lt_irrefl _)
  all_goals try (rcases hty with h' | h' <;> rw [h'] at h1 <;> cases h1)
  rcases hpre with ⟨hlt, -⟩ | ⟨-, rfl⟩ | ⟨hlt, -⟩
  · rw [ht] at hlt; exact absurd hlt (Int.lt_irrefl _)
  · exact hh
  · rw [ht] at hlt; exact absurd hlt (Int.lt_irrefl _)

/-- **`RecvEnd` of a self-acknowledgement or a self-vote** (any term): nothing (stale), the type
switch at the state (a local message), or the preamble then the type switch. -/
theorem recvEnd_resp {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hty : m.ty = .appResp ∨ m.ty = .voteResp) (h : RecvEnd k c id s m s') :
    s' = s ∨ (m.term = W64 0 ∧ HandleEnd k c id s m s') ∨
      (m.term ≠ W64 0 ∧ ¬ PreTermKeep m ∧ ∃ s1, PreEnd k s m s1 ∧ HandleEnd k c id s1 m s') := by
  have hk : ¬ PreTermKeep m := by
    rintro (h1 | ⟨h1, -⟩) <;> rcases hty with h' | h' <;> rw [h'] at h1 <;> cases h1
  rcases h with ⟨h0, hh⟩ | ⟨-, -, hst⟩ | ⟨-, ⟨-, h1 | h1, -⟩, -⟩ | ⟨h0, s1, hpre, hh⟩
  · exact .inr (.inl ⟨h0, hh⟩)
  · rcases hst with rfl | ⟨-, h1 | h1, -⟩ | ⟨h1, -⟩
    · exact .inl rfl
    all_goals (rcases hty with h' | h' <;> rw [h'] at h1 <;> cases h1)
  all_goals try (rcases hty with h' | h' <;> rw [h'] at h1 <;> cases h1)
  exact .inr (.inr ⟨h0, hk, s1, hpre, hh⟩)

/-- A granted pre-vote response's step: nothing, or at a follower with no leader the campaign
(`PreTermKeep`: no term adopted). -/
theorem recvEnd_preGrant {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hty : m.ty = .preVoteResp) (hrj : m.reject = false) (h : RecvEnd k c id s m s') :
    s' = s ∨ (s.role = .follower ∧ s.lead = W64 0 ∧ CampaignSends c id s [] s') := by
  have hh : ∀ {s1 : PState}, HandleEnd k c id s1 m s' → s1 = s →
      s' = s ∨ (s.role = .follower ∧ s.lead = W64 0 ∧ CampaignSends c id s [] s') := by
    rintro s1 hh rfl
    rcases handleEnd_preVoteResp hty hh with h | ⟨h1, h2, -, h3⟩
    · exact .inl h
    · exact .inr ⟨h1, h2, h3⟩
  rcases h with ⟨-, h1⟩ | ⟨-, -, hst⟩ | ⟨-, hli, rfl⟩ | ⟨-, s1, hpre, h1⟩
  · exact hh h1 rfl
  · rcases hst with rfl | ⟨-, happ, -⟩ | ⟨hpv, -⟩
    · exact .inl rfl
    · rw [hty] at happ; rcases happ with h' | h' <;> cases h'
    · rw [hty] at hpv; cases hpv
  · exact .inl rfl
  · rcases hpre with ⟨-, hk, -⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact absurd (.inr ⟨hty, hrj⟩) hk
    · exact hh h1 rfl
    · exact hh h1 rfl

/-- **`Advance` of a pre-candidate's self pre-votes** (granted pre-vote responses): nothing, or the
campaign at a follower with no leader (`CampaignSends`; the candidate then ignores the rest). -/
theorem advanceEnd_pre {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (hq : ∀ q ∈ qs, q.ty = .preVoteResp ∧ q.reject = false) (h : AdvanceEnd k c id s qs s') :
    s' = s ∨ (s.role = .follower ∧ s.lead = W64 0 ∧ CampaignSends c id s [] s') := by
  induction h with
  | nil s => exact .inl rfl
  | cons s s1 s' q qs hr hrest ih =>
    obtain ⟨hty, hrj⟩ := hq q List.mem_cons_self
    have ih' := ih (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq'))
    rcases recvEnd_preGrant hty hrj hr with rfl | ⟨hfl, hld, hcs⟩
    · exact ih'
    · refine .inr ⟨hfl, hld, ?_⟩
      have hc : s1.role = .candidate := by
        obtain ⟨peers, -, rfl⟩ := hcs; rfl
      have : s' = s1 := by
        rcases ih' with h' | ⟨h', -⟩
        · exact h'
        · rw [hc] at h'; cases h'
      rw [this]; exact hcs

/-! ## `Advance` and `Reach` read on the protocol state below `mskB1` -/

/-- **`QsOk` of a message other than a pre-vote response**: the S4 shape, a self-acknowledgement
or a self-vote at the node's term. -/
theorem QsOk.notPre {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (h : QsOk R S n v q) (hq : q.ty ≠ .preVoteResp) :
    q.src = nodeId n ∧ q.dst = nodeId n ∧ q.term = v.ps.term ∧ q.reject = false ∧
    ((q.ty = .appResp ∧ v.ps.role = .leader ∧
        AckIn S (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z v.ps.term) (uint.Z q.index)) ∨
     (q.ty = .voteResp ∧
        { voter := nameOf (nodeId n), term := uint.Z v.ps.term, cand := nameOf (nodeId n) } ∈ S.votes)) := by
  obtain ⟨h1, h2, h3, ⟨h4, h5⟩ | ⟨h6, -⟩⟩ := h
  · exact ⟨h1, h2, h4, h3, h5⟩
  · exact absurd h6 hq

/-- `Advance` over `RState` is `Advance` over the protocol state at the node's configuration (the
received messages keep the configuration, the storage acknowledgements the protocol state). -/
theorem advanceEndR_toP {Adm : List EntryM → CCState → Prop} {dec : CCDec} {k : NodeK} {id : w64}
    {r r' : RState} {qs : List Msg} (h : AdvanceEndR Adm dec k id r qs r') :
    AdvanceEnd k r.cfg.cfg id r.p qs r'.p := by
  induction h with
  | nil r r' ha =>
    have : r'.p = r.p := by
      rcases ha with rfl | ⟨a, -, rfl⟩ | ⟨j, sn, cs', -, rfl⟩ <;> rfl
    rw [this]; exact .nil _
  | cons r r1 r' q qs hr _ ih =>
    have hc : r1.cfg = r.cfg := hr.2.1.2.2
    rw [hc] at ih
    exact .cons _ _ _ q qs hr.1 ih

/-- **`Advance` of a view's queue** (`QsOk`, homogeneous): of self-acknowledgements and self-votes
(no pre-vote response queued); of a pre-candidate's self pre-votes (a voter's, pre-vote on), nothing or
the campaign at a follower with no leader (`advanceEnd_pre`). -/
theorem AdvanceEnd.split {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {k : NodeK}
    {c : CfgM} {s' : PState} (hqs : ∀ q ∈ v.qs, QsOk R S n v q)
    (h : AdvanceEnd k c (nodeId n) v.ps v.qs s') :
    (∀ q ∈ v.qs, q.ty ≠ .preVoteResp) ∨
    ((∀ q ∈ v.qs, q.ty = .preVoteResp ∧ q.reject = false) ∧ nodeId n ∈ v.r.cfg.cfg.voters ∧
      (R.k n).prevote = true ∧
      (s' = v.ps ∨ (v.ps.role = .follower ∧ v.ps.lead = W64 0 ∧ CampaignSends c (nodeId n) v.ps [] s'))) := by
  by_cases hex : ∃ q ∈ v.qs, q.ty = .preVoteResp
  · obtain ⟨q, hq, hty⟩ := hex
    obtain ⟨-, -, -, ⟨-, h1 | h1⟩ | ⟨-, -, hvt, hpv, hall⟩⟩ := hqs q hq
    · rw [hty] at h1; cases h1.1
    · rw [hty] at h1; cases h1.1
    have hpr : ∀ q ∈ v.qs, q.ty = .preVoteResp ∧ q.reject = false :=
      fun q' hq' => ⟨hall q' hq', (hqs q' hq').2.2.1⟩
    exact .inr ⟨hpr, hvt, hpv, advanceEnd_pre hpr h⟩
  · exact .inl fun q hq hty => hex ⟨q, hq, hty⟩

/-- The `by` of a drain whose input steps as a tick (`TickEnd`): a tick, or `Campaign`
(`tickEndR_of_campaignEndR'`). -/
def TickBy (b : AntCheck.Str) : Prop := b = go!"tick" ∨ b = go!"campaign"

/-- **`Reach` read on the protocol state** (below `mskB1`: the inputs a message received, a tick,
a proposal or a read request, the configuration `c` fixed): no input; a received message (sent to
the node, of a nonzero term but a forwarded read request) stepped (`RecvEnd`): of a type the S4 and
read paths read (`RdTy`), or a pre-vote request or response (a granted response to a voter); a tick
stepped (`TickEnd`); a proposal (`ProposeEnd`); a read request (`ReadIdxEnd` at `readMsg`);
`Advance` stepping the queued self-acknowledgements and self-votes (`AdvanceEnd`), or a voter's
queued self pre-votes: nothing or the campaign (`AdvanceEnd.split`); a leader's appends
(`SendsEnd`: a transfer, a transfer message received at the node's term); a transfer message
received (`xnet`) of a higher term adopted (a follower with no leader); a `MsgTimeoutNow`
received, at the node's term or after adopting its higher one, starting at a follower the
transfer's campaign (`CampaignEnd` at `ctxTransfer`). The other transfer steps change nothing (`stay`), as does
`ReportUnreachable`. -/
inductive ReachP (kk : NodeK) (c : CfgM) (id : w64) (net : List Msg) (xnet : List XMsg) :
    NodeView → PState → Prop
  | stay (v : NodeView) : v.Idle → DrainBy v.byE → ReachP kk c id net xnet v v.ps
  | recv (v : NodeView) (m : Msg) (ps₁ : PState) : v.Idle → v.byE = go!"recv" → v.cause = some m →
      m ∈ net → m.dst = id → (m.ty ≠ .readIndex → m.term ≠ W64 0) → RdTy m.ty →
      RecvEnd kk c id v.ps m ps₁ → ReachP kk c id net xnet v ps₁
  | recvP (v : NodeView) (m : Msg) (ps₁ : PState) : v.Idle → v.byE = go!"recv" → v.cause = some m →
      m ∈ net → m.dst = id → m.term ≠ W64 0 → (m.ty = .preVote ∨ m.ty = .preVoteResp) →
      (m.ty = .preVoteResp → m.reject = false → id ∈ c.voters) →
      RecvEnd kk c id v.ps m ps₁ → ReachP kk c id net xnet v ps₁
  | tick (v : NodeView) (ps₁ : PState) : v.Idle → TickBy v.byE → TickEnd kk c id v.ps ps₁ →
      ReachP kk c id net xnet v ps₁
  | propose (v : NodeView) (d : List w8) (ps₁ : PState) : v.Idle → v.byE = go!"propose" →
      ProposeEnd c id v.ps (propMsg id d) ps₁ → ReachP kk c id net xnet v ps₁
  | read (v : NodeView) (d : List w8) (ps₁ : PState) : v.Idle → v.byE = go!"read" →
      ReadIdxEnd c id v.ps (readMsg d) ps₁ → ReachP kk c id net xnet v ps₁
  | advance (v : NodeView) (ps₁ : PState) : v.pend = [] → v.ce = [] → DrainBy v.byE →
      (∀ q ∈ v.qs, q.ty ≠ .preVoteResp) → AdvanceEnd kk c id v.ps v.qs ps₁ → ReachP kk c id net xnet v ps₁
  | advP (v : NodeView) (ps₁ : PState) : v.pend = [] → v.ce = [] → DrainBy v.byE →
      (∀ q ∈ v.qs, q.ty = .preVoteResp ∧ q.reject = false) → id ∈ c.voters → kk.prevote = true →
      (ps₁ = v.ps ∨ (v.ps.role = .follower ∧ v.ps.lead = W64 0 ∧ CampaignSends c id v.ps [] ps₁)) →
      ReachP kk c id net xnet v ps₁
  | sends (v : NodeView) (ps₁ : PState) : v.Idle → DrainBy v.byE → v.ps.role = .leader →
      SendsEnd c id v.ps ps₁ → ReachP kk c id net xnet v ps₁
  | adoptX (v : NodeView) (x : XMsg) : v.Idle → v.byE = go!"recv" → v.xcause = some x → x ∈ xnet →
      x.dst = id → uint.Z v.ps.term < uint.Z x.term →
      ReachP kk c id net xnet v (pbecomeFollower v.ps x.term (W64 0))
  | campX (v : NodeView) (x : XMsg) (p1 ps₁ : PState) : v.Idle → v.byE = go!"recv" →
      v.xcause = some x → x ∈ xnet → x.dst = id → x.ty = .timeoutNow →
      ((uint.Z v.ps.term < uint.Z x.term ∧ p1 = pbecomeFollower v.ps x.term (W64 0)) ∨
        (x.term = v.ps.term ∧ p1 = v.ps)) →
      p1.role = .follower → CampaignEnd c id p1 ctxTransfer ps₁ → ReachP kk c id net xnet v ps₁

/-- A local proposal's step (term `0`: no preamble) is `ProposeEnd`. -/
theorem recvEnd_propMsg {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {d : List w8}
    (h : RecvEnd k c id s (propMsg id d) s') : ProposeEnd c id s (propMsg id d) s' := by
  rcases h with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · simp only [HandleEnd, propMsg] at hh; exact hh
  all_goals exact absurd rfl h0

/-- A local read request's step (term `0`: no preamble) is `ReadIdxEnd`. -/
theorem recvEnd_readMsg {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {d : List w8}
    (h : RecvEnd k c id s (readMsg d) s') : ReadIdxEnd c id s (readMsg d) s' := by
  rcases h with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · simp only [HandleEnd, readMsg] at hh; exact hh
  all_goals exact absurd rfl h0

/-- `TransferEndR`'s protocol state: kept, or a leader's appends. -/
theorem transferEndR_p {id to : w64} {r r' : RState} (h : TransferEndR id r to r') :
    r'.p = r.p ∨ (r.p.role = .leader ∧ SendsEnd r.cfg.cfg id r.p r'.p) := by
  obtain ⟨-, -, -, -, -, -, h | ⟨hl, -, -, hs⟩⟩ := h
  · exact .inl h
  · exact .inr ⟨hl, hs⟩

/-- **`ReachIn` below `mskB1` is its protocol reading** at the node's configuration. -/
theorem ReachIn.toP {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {net : List Msg} {xnet : List XMsg} {n : Fin R.N}
    {S : AntCheck.State} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    ReachP (R.k n) v.r.cfg.cfg (nodeId n) net xnet v r₁.p := by
  obtain ⟨hmd, -, -, -, -, hty⟩ := hin.b1 hmsk
  have hcc : R.md.confChanges = false := by rw [hmd]
  cases hr with
  | stay hi hb => exact .stay _ hi hb
  | input inp _ hinp hi hbe hca hxc hm hx hs =>
    rcases Input.step_b1 hmsk hinp hs with ⟨m, rfl⟩ | ⟨hti, hs⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩ | ⟨x, rfl⟩ |
        ⟨to, rfl⟩ | ⟨⟨t, rfl⟩, rfl⟩
    · obtain ⟨hmn, hmd', hm0⟩ := hm m rfl
      have hne : ∀ {t : MsgType}, m.ty = t → (t = .preVote ∨ t = .preVoteResp) → m.term ≠ W64 0 :=
        fun he ht => hm0 (by rw [he]; rcases ht with rfl | rfl <;> nofun)
      rcases hty m hmn with h4 | hpt | hpt
      · exact .recv _ m _ hi hbe hca hmn hmd' hm0 h4 hs.1
      · exact .recvP _ m _ hi hbe hca hmn hmd' (hne hpt (.inl rfl)) (.inl hpt)
          (fun h1 => by rw [hpt] at h1; cases h1) hs.1
      · refine .recvP _ m _ hi hbe hca hmn hmd' (hne hpt (.inr rfl)) (.inr hpt) (fun h1 h2 => ?_) hs.1
        have := ((hnet.2.2.2.2.2 m hmn) hcc).2 h1 h2
        rw [(hv.facts.conf0 hcc).1, CfgM.voters_simple, ← hmd']; exact this
    · have hti' : TickBy v.byE := by rcases hti with rfl | rfl <;> simp [hbe, Input.byE, TickBy]
      exact .tick _ _ hi hti' hs.1
    · exact .propose _ d _ hi hbe (recvEnd_propMsg hs.1)
    · exact .read _ d _ hi hbe (recvEnd_readMsg hs.2.1)
    · obtain ⟨hxn, hxd⟩ := hx x rfl
      have hdb : DrainBy v.byE := .inr ⟨.recvX x, hbe⟩
      have hxc' : v.xcause = some x := hxc
      rcases hs with ⟨hty, ⟨-, rfl⟩ | ⟨hle, ⟨p1, hp1, hend⟩, -⟩⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, hT⟩ | ⟨hlt, rfl⟩⟩
      · exact .stay _ hi hdb
      · rcases hend with he | ⟨hl, hse⟩ | hce
        · rw [he]
          rcases hp1 with ⟨hlt, rfl⟩ | ⟨-, rfl⟩
          · exact .adoptX _ x hi hbe hxc' hxn hxd hlt
          · exact .stay _ hi hdb
        · rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact absurd hl (by simp [pbecomeFollower])
          · exact .sends _ _ hi hdb hl hse
        · exact .campX _ x p1 _ hi hbe hxc' hxn hxd hty hp1 hce.1 hce.2
      · exact .stay _ hi hdb
      · rcases transferEndR_p hT with he | ⟨hl, hse⟩
        · rw [he]; exact .stay _ hi hdb
        · exact .sends _ _ hi hdb hl hse
      · exact .adoptX _ x hi hbe hxc' hxn hxd hlt
    · rcases transferEndR_p hs with he | ⟨hl, hse⟩
      · rw [he]; exact .stay _ hi (.inr ⟨.transfer to, hbe⟩)
      · exact .sends _ _ hi (.inr ⟨.transfer to, hbe⟩) hl hse
    · exact .stay _ hi (.inr ⟨.unreachable t, hbe⟩)
  | advance _ hpd _ hce _ hb ha _ =>
    rcases AdvanceEnd.split hv.qs (advanceEndR_toP ha) with hno | ⟨hpr, hvt, hpv, h⟩
    · exact .advance _ _ hpd hce hb hno (advanceEndR_toP ha)
    · exact .advP _ _ hpd hce hb hpr hvt hpv h

end inputs

end AntSim
end EtcdGrove
end Perennial
