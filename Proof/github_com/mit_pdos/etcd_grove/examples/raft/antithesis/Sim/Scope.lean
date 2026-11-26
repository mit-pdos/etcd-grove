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
(`Input.InMask`). Each migrated statement is `antSim_X_in msk (hmsk : msk ≤ mskB1a)` (parity B1, stage A); B1 widens it to
`mskB1`, and at `mskTop` it gives the plain `antSim_X : antSim_X.stmt` (`ReachIn.ofReach_top`).
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

/-- Parity B1's scope: pre-vote, check quorum, reads, transfer, non-voters, each node's flags,
`Campaign`, `ReportUnreachable`; sync storage, no snapshot, no conf change, no driver mode. -/
def mskB1 : SimMask :=
  { md := { prevote := true, cq := true, reads := true, transfer := true, nonVoters := true },
    k := { prevote := true, cq := true, sdr := true }, campaign := true, unreachable := true }

/-- **Parity B1, stage A**: `mskS4` with `Campaign` and non-voters (servers outside the initial
configuration, `R.K < R.N`). B1's other run freedoms need no mask field, as no statement reads
them: duplication (`R.drv.maxDeliveries`: a message received stays on the network, so it can be
received again), the limits (`MaxInflightMsgs`, `MaxSizePerMsg`: the relations admit any
`SendOk` sends) and bootstrapping (`R.boot`: every statement is over every `R`). -/
def mskB1a : SimMask := { md := { nonVoters := true }, campaign := true }

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
  | stay (v : NodeView) : v.Idle → ReachIn msk R dec Adm net xnet n v v.r
  | input (v : NodeView) (inp : Input) (r₁ : RState) :
      inp.InMask msk →
      v.Idle → v.byE = inp.byE → v.cause = inp.cause → v.xcause = inp.xcause →
      (∀ m, inp = .recv m → m ∈ net ∧ m.dst = nodeId n ∧ m.term ≠ W64 0) →
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
  | stay h1 => exact .stay _ h1
  | input inp _ h0 h1 h2 h3 h4 h5 h6 h7 => exact .input _ inp _ h1 h2 h3 h4 h5 h6 h7
  | advance _ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

theorem Input.inMask_top [GooseExts] (inp : Input) : inp.InMask mskTop := by
  cases inp <;> simp [Input.InMask, mskTop]

theorem ReachIn.ofReach_top {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : NodeView} {r₁ : RState}
    (h : Reach R dec Adm net xnet n v r₁) : ReachIn mskTop R dec Adm net xnet n v r₁ := by
  cases h with
  | stay h1 => exact .stay _ h1
  | input inp _ h1 h2 h3 h4 h5 h6 h7 => exact .input _ inp _ (Input.inMask_top inp) h1 h2 h3 h4 h5 h6 h7
  | advance _ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

theorem QuietIn.ofQuiet_top {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v v' : NodeView}
    (h : Quiet R dec Adm net xnet n v v') : QuietIn mskTop R dec Adm net xnet n v v' := by
  cases h with
  | input inp h1 h2 h3 => exact .input _ inp (Input.inMask_top inp) h1 h2 h3
  | noReady _ h1 h2 h3 h4 h5 h6 h7 h8 => exact .noReady _ _ (ReachIn.ofReach_top h1) h2 h3 h4 h5 h6 h7 h8
  | silentReady _ _ h1 h2 h3 => exact .silentReady _ _ _ (ReachIn.ofReach_top h1) h2 h3

/-- Below `mskB1a`, the mask admits only recv, tick, propose and campaign. -/
theorem Input.inMask_b1a {msk : SimMask} (hmsk : msk ≤ mskB1a) {inp : Input} (h : inp.InMask msk) :
    (∃ m, inp = .recv m) ∨ inp = .tick ∨ (∃ d, inp = .propose d) ∨ inp = .campaign := by
  obtain ⟨⟨_, _, h3, h4, _, h6, h7, h8, _⟩, _, _, h12, _⟩ := hmsk
  cases inp <;> simp_all [Input.InMask, BLe, mskB1a]

/-- `RawNode.Campaign` with pre-vote off is `TickEnd`'s campaign (an election's requests carry no
context) or nothing: a tick's step. -/
theorem tickEndR_of_campaignEndR {k : NodeK} {id : w64} {r r' : RState} (hk : k.prevote = false)
    (h : CampaignEndR k id r r') : TickEndR k id r r' := by
  obtain ⟨h0 | ⟨hnl, -, -, ⟨-, hce⟩ | ⟨hk', -⟩⟩, hkc, hfp, hsn, hpci⟩ := h
  · subst h0; exact ⟨.inl rfl, hkc, hfp, hsn, hpci⟩
  · exact ⟨.inr (.inl ⟨hnl, hk, hce⟩), hkc, hfp, hsn, hpci⟩
  · rw [hk] at hk'; cases hk'

/-- Below `mskB1a`, the run has no feature but non-voters, no node flag and no driver mode, and its
network only the S4 types. -/
theorem InMask.b1a {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {net : List Msg}
    {xnet : List XMsg} (h : InMask msk R net xnet) :
    R.md = { nonVoters := R.md.nonVoters } ∧ (∀ n, R.k n = {}) ∧ R.drv.batch = false ∧
    R.drv.parallel = false ∧ R.drv.split = 0 ∧
    R.drv.restarts = false ∧ xnet = [] ∧
    ∀ m ∈ net, m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨
      m.ty = .heartbeat ∨ m.ty = .heartbeatResp ∨ m.ty = .propose := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, ⟨k1, k2, k3⟩, c1, c2, c3, c4, c5, c6⟩ := hmsk
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩, hk, d1, d2, d3, d4, hnet, hx⟩ := h
  simp only [BLe, mskB1a] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hR : R.md; simp_all
  · intro n; obtain ⟨e1, e2, e3⟩ := hk n; simp only [BLe] at e1 e2 e3
    cases hn : R.k n; simp_all
  · cases h : R.drv.batch <;> simp_all
  · cases h : R.drv.parallel <;> simp_all
  · cases h : R.drv.split with
    | zero => rfl
    | succ _ => exact absurd (d3 (by simp [h])) (by simp_all)
  · cases h : R.drv.restarts <;> simp_all
  · cases h : msk.md.transfer <;> simp_all
  · intro m hm; rcases hnet m hm with h | h
    · simp only [NetTy] at h
      rcases h with h | h | h | h | h | h | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp_all
    · simp [h]

/-- **An input below `mskB1a`, read as one below `mskS4`**: a message received, a proposal, or a
tick's step (a tick, or `Campaign` with pre-vote off: `tickEndR_of_campaignEndR`). -/
theorem Input.step_b1a {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {net : List Msg} {xnet : List XMsg} {n : Fin R.N}
    {r r₁ : RState} {inp : Input} (hin : AntSim.InMask msk R net xnet)
    (h : inp.InMask msk) (hs : InputStep R dec Adm n r inp r₁) :
    (∃ m, inp = .recv m) ∨ ((inp = .tick ∨ inp = .campaign) ∧ InputStep R dec Adm n r .tick r₁) ∨
      ∃ d, inp = .propose d := by
  rcases Input.inMask_b1a hmsk h with ⟨m, rfl⟩ | rfl | ⟨d, rfl⟩ | rfl
  · exact .inl ⟨m, rfl⟩
  · exact .inr (.inl ⟨.inl rfl, hs⟩)
  · exact .inr (.inr ⟨d, rfl⟩)
  · exact .inr (.inl ⟨.inr rfl, tickEndR_of_campaignEndR (by rw [(hin.b1a hmsk).2.1 n]) hs⟩)

/-! ## The end relations read below `mskB1a`

The per-input end relations as the S4 Sim proofs read them (`InputEnd.lean` before parity B1's
new arms), and their derivation from the relations at the runs and inputs a mask below `mskB1a`
admits: no node flag (no lease, no stale answer, no pre-campaign, no step-down), the S4 types (no
pre-vote, read-index or snapshot message), a heartbeat response with no context (no read
acknowledgement) and no deferred read request (no release on a commit). Parity B1's stage B widens
the mask by proving the new arms, these readings with them. -/

/-- `PreEnd` below `mskB1a` (no pre-vote message). -/
def PreEndO (_k : NodeK) (s : PState) (m : Msg) (s1 : PState) : Prop :=
  (uint.Z s.term < uint.Z m.term ∧
    s1 = pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0)) ∨
  (m.term = s.term ∧ s1 = s)

/-- `AppRespEnd` below `mskB1a` (no deferred read request to release). -/
def AppRespEndO (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (s.matched !! m.src = none ∧ s' = s) ∨
  (m.reject = true ∧ s.matched !! m.src ≠ none ∧ SendsEnd c id s s') ∨
  (m.reject = false ∧ ∃ (x n : w64), s.matched !! m.src = some x ∧
    (n = s.commit ∨
      PCommitOk c { s with matched :=
        <[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched } n) ∧
    SendsEnd c id { s with
      matched := <[m.src := if uint.Z x < uint.Z m.index then m.index else x]> s.matched,
      commit := n } s')


/-- `HandleEnd` below `mskB1a` (the S4 types; a heartbeat response with no context). -/
def HandleEndO (_k : NodeK) (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  match m.ty with
  | .vote =>
    (PCanVote s m.src ∧ plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true ∧
      s' = psendMsgs { s with vote := m.src } [Msg.plain .voteResp id m.src m.term false]) ∨
    (¬ (PCanVote s m.src ∧ plogUpToDate s.base s.log (entryID.mk m.logterm m.index) = true) ∧
      s' = psendMsgs s [Msg.plain .voteResp id m.src s.term true])
  | .voteResp =>
    if s.role = .candidate then
      (¬ JLost c (recordVote s.votes m.src (!m.reject)) ∧
        s' = { s with votes := recordVote s.votes m.src (!m.reject) }) ∨
      (JQuorum c (granted (recordVote s.votes m.src (!m.reject))) ∧
        WinEnd c id { s with votes := recordVote s.votes m.src (!m.reject) } s') ∨
      (JLost c (recordVote s.votes m.src (!m.reject)) ∧
        s' = pbecomeFollower { s with votes := recordVote s.votes m.src (!m.reject) } s.term
               (W64 0))
    else s' = s
  | .app => if s.role = .leader then s' = s else AppEnd id (padoptLeader s m.src) m s'
  | .heartbeat =>
    if s.role = .leader then s' = s
    else s' = psendMsgs { padoptLeader s m.src with commit := plogCommitTo s.commit m.commit }
                [{ Msg.plain .heartbeatResp id m.src s.term false with ctx := m.ctx }]
  | .appResp => if s.role = .leader then AppRespEndO c id s m s' else s' = s
  | .heartbeatResp => if s.role = .leader then SendsEnd c id s s' else s' = s
  | .propose => ProposeEnd c id s m s'
  | _ => ∃ (B : Int) (r : List Msg), StepC c id B s r s'


/-- `RecvEnd` below `mskB1a`: a local message's step, a stale one ignored, or the preamble then
the step. -/
def RecvEndO (k : NodeK) (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (m.term = W64 0 ∧ HandleEndO k c id s m s') ∨
  (m.term ≠ W64 0 ∧ uint.Z m.term < uint.Z s.term ∧ s' = s) ∨
  (m.term ≠ W64 0 ∧ ∃ s1, PreEndO k s m s1 ∧ HandleEndO k c id s1 m s')

/-- `TickEnd` below `mskB1a`: nothing, a campaign, a leader's heartbeats. -/
def TickEndO (_k : NodeK) (c : CfgM) (id : w64) (s s' : PState) : Prop :=
  s' = s ∨
  (s.role ≠ .leader ∧ id ∈ c.voters ∧
    ∃ (peers : List w64) (cl : List w8), peers ≡ₚ elements (c.voters \ {[id]}) ∧
      s' = psendMsgs (pbecomeCandidate id s)
        ([Msg.plain .voteResp id id (s.term + W64 1) false] ++
         peers.map (fun d => pvoteReq id d (s.term + W64 1) (plogLast s.base s.log) cl))) ∨
  (s.role = .leader ∧ ∃ ms : List Msg, (∀ x ∈ ms, HeartbeatOk id s x ∧ x.index = W64 0 ∧ x.logterm = W64 0 ∧ x.entries = [] ∧
      x.ctx = hbCtx s.rd.ro ∧ x.dst ∈ c.ids) ∧ s' = psendMsgs s ms)

/-- `AdvanceEnd` over `RecvEndO`. -/
inductive AdvanceEndO (k : NodeK) (c : CfgM) (id : w64) : PState → List Msg → PState → Prop
  | nil (s : PState) : AdvanceEndO k c id s [] s
  | cons (s s1 s' : PState) (q : Msg) (qs : List Msg) :
      RecvEndO k c id s q s1 → AdvanceEndO k c id s1 qs s' → AdvanceEndO k c id s (q :: qs) s'

/-- The S4 types (`InMask.b1a`'s network, and a proposal). -/
def S4Ty (t : MsgType) : Prop :=
  t = .app ∨ t = .appResp ∨ t = .vote ∨ t = .voteResp ∨ t = .heartbeat ∨ t = .heartbeatResp ∨
    t = .propose

theorem not_preTy {m : Msg} (hty : S4Ty m.ty) :
    ¬ (m.ty = .preVote ∨ (m.ty = .preVoteResp ∧ m.reject = false)) := by
  rintro (h | ⟨h, -⟩) <;> rcases hty with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h

theorem pend_nil_eta {X : PState} (h : X.rd.pend = []) : { X with rd := { X.rd with pend := [] } } = X := by
  rw [← h]

theorem preEndO_of {k : NodeK} {s s1 : PState} {m : Msg} (hty : S4Ty m.ty) (h : PreEnd k s m s1) :
    PreEndO k s m s1 := by
  rcases h with ⟨hlt, -, rfl⟩ | h2 | ⟨-, hpk, -⟩
  · exact .inl ⟨hlt, rfl⟩
  · exact .inr h2
  · exact absurd hpk (not_preTy hty)

theorem preEnd_pend {k : NodeK} {s s1 : PState} {m : Msg} (h : PreEnd k s m s1) :
    s1.rd.pend = s.rd.pend := by
  rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl

theorem appRespEndO_of {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hp : s.rd.pend = [])
    (h : AppRespEnd c id s m s') : AppRespEndO c id s m s' := by
  rcases h with h | h | h | ⟨hrj, x, n, s2, hx, hpc, hrel, hse⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · refine .inr (.inr ⟨hrj, x, n, hx, .inr hpc, ?_⟩)
    obtain ⟨t, v, l, r, vs, ob, b, lg, cm, mt, ⟨st, ro, pd⟩⟩ := s
    simp only at hp; subst hp
    rcases hrel with ⟨-, hb, hbok, rfl⟩ | ⟨-, rfl⟩
    · have hb0 : hb = [] := by
        cases hb with
        | nil => rfl
        | cons y _ =>
          obtain ⟨-, k, hk0, hk, -⟩ := hbok y List.mem_cons_self
          simp only [List.length_nil] at hk; omega
      subst hb0
      simpa [psendMsgs, readonlyRelease] using hse
    · simpa [preadRespondAll] using hse

theorem handleEndO_of {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hty : S4Ty m.ty)
    (hctx : m.ty = .heartbeatResp → m.ctx = []) (hp : s.rd.pend = []) (h : HandleEnd k c id s m s') :
    HandleEndO k c id s m s' := by
  rcases hty with h1 | h1 | h1 | h1 | h1 | h1 | h1
  all_goals simp only [HandleEnd, HandleEndO, h1] at h ⊢
  all_goals try exact h
  · by_cases hl : s.role = .leader
    · rw [if_pos hl] at h ⊢; exact appRespEndO_of hp h
    · rw [if_neg hl] at h ⊢; exact h
  · by_cases hl : s.role = .leader
    · rw [if_pos hl] at h ⊢
      obtain ⟨s2, hs2, ⟨-, rfl⟩ | ⟨hne, -⟩⟩ := h
      · exact hs2
      · exact absurd (hctx h1) hne
    · rw [if_neg hl] at h ⊢; exact h

/-- **`RecvEnd` below `mskB1a`** (no node flag, an S4 type, no context on a heartbeat response, no
deferred read request) is its reading. -/
theorem recvEndO_of {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hk : k = {})
    (hty : S4Ty m.ty) (hctx : m.ty = .heartbeatResp → m.ctx = []) (hp : s.rd.pend = [])
    (h : RecvEnd k c id s m s') : RecvEndO k c id s m s' := by
  subst hk
  rcases h with ⟨h0, hh⟩ | ⟨h0, hlt, hst⟩ | ⟨-, hli, -⟩ | ⟨h0, s1, hpre, hh⟩
  · exact .inl ⟨h0, handleEndO_of hty hctx hp hh⟩
  · rcases hst with rfl | ⟨hc, -⟩ | ⟨hpv, -⟩
    · exact .inr (.inl ⟨h0, hlt, rfl⟩)
    · simp at hc
    · rcases hty with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at hpv <;> cases hpv
  · exact absurd hli.1 (by decide)
  · exact .inr (.inr ⟨h0, s1, preEndO_of hty hpre,
      handleEndO_of hty hctx ((preEnd_pend hpre).trans hp) hh⟩)

/-- **`TickEnd` with no node flag** is its reading. -/
theorem tickEndO_of {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} (hk : k = {})
    (h : TickEnd k c id s s') : TickEndO k c id s s' := by
  subst hk
  rcases h with h | ⟨hnl, -, hid, peers, hperm, heq⟩ | ⟨-, h1, -⟩ | h4 | ⟨-, h5, -⟩
  · exact .inl h
  · exact .inr (.inl ⟨hnl, hid, peers, [], hperm, heq⟩)
  · cases h1
  · exact .inr (.inr h4)
  · cases h5

/-- A step of `Advance`'s self-messages keeps the deferred read requests. -/
theorem recvEndO_pend_self {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {q : Msg}
    (hq : q.ty = .appResp ∨ q.ty = .voteResp) (h : RecvEndO k c id s q s') :
    s'.rd.pend = s.rd.pend := by
  have hh : ∀ {s1 : PState}, HandleEndO k c id s1 q s' → s'.rd.pend = s1.rd.pend := by
    intro s1 hh
    rcases hq with h1 | h1 <;> simp only [HandleEndO, h1] at hh
    · split at hh
      · rcases hh with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨-, x, n, -, -, ms, -, rfl⟩ <;> rfl
      · rw [hh]
    · split at hh
      · rcases hh with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
      · rw [hh]
  rcases h with ⟨-, hh'⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh'⟩
  · exact hh hh'
  · rfl
  · rw [hh hh']
    rcases hpre with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- **`AdvanceEnd` with no node flag** (self-acknowledgements and self-votes, no deferred read
request) is its reading. -/
theorem advanceEndO_of {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (hk : k = {}) (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp) (hp : s.rd.pend = [])
    (h : AdvanceEnd k c id s qs s') : AdvanceEndO k c id s qs s' := by
  induction h with
  | nil s => exact .nil s
  | cons s s1 s' q qs hr _ ih =>
    have hq0 := hq q List.mem_cons_self
    have hty : S4Ty q.ty := by rcases hq0 with h | h <;> simp [S4Ty, h]
    have hr' := recvEndO_of hk hty (fun h => by rcases hq0 with h' | h' <;> rw [h'] at h <;> cases h) hp hr
    exact .cons _ _ _ q qs hr'
      (ih (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')) ((recvEndO_pend_self hq0 hr').trans hp))

/-- **A message received from the network, below `mskB1a`**: its step from the view is the
reading (`recvEndO_of`: an S4 type and no context on a heartbeat response, `InMask.b1a`/`MsgMask`;
no deferred read request, `NodeFacts.pend0`). -/
theorem RecvEnd.toO_in {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {S : AntCheck.State} {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : NodeView} {m : Msg}
    {c : CfgM} {s' : PState} (hin : InMask msk R net xnet) (hnet : NetOk R S net)
    (hv : NodeOk R dec S net n v) (hm : m ∈ net) (h : RecvEnd (R.k n) c (nodeId n) v.ps m s') :
    RecvEndO (R.k n) c (nodeId n) v.ps m s' := by
  obtain ⟨hmd, hk, -, -, -, -, -, hty⟩ := hin.b1a hmsk
  have hrd : R.md.reads = false := by rw [hmd]
  exact recvEndO_of (hk n) (hty m hm) (fun h1 => (hnet.2.2.2.2.1 m hm).2.2.2 hrd (.inr h1))
    (hv.facts.pend0 hrd) h

/-- **A proposal below `mskB1a`**: its step from the view is the reading. -/
theorem RecvEnd.toO_prop {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {S : AntCheck.State} {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : NodeView}
    {d : List w8} {c : CfgM} {s' : PState} (hin : InMask msk R net xnet) (hv : NodeOk R dec S net n v)
    (h : RecvEnd (R.k n) c (nodeId n) v.ps (propMsg (nodeId n) d) s') :
    RecvEndO (R.k n) c (nodeId n) v.ps (propMsg (nodeId n) d) s' := by
  obtain ⟨hmd, hk, -⟩ := hin.b1a hmsk
  exact recvEndO_of (hk n) (by simp [S4Ty, propMsg]) (fun h1 => by simp [propMsg] at h1)
    (hv.facts.pend0 (by rw [hmd])) h

/-- **A tick below `mskB1a`** is the reading. -/
theorem TickEnd.toO_in {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {net : List Msg}
    {xnet : List XMsg} {n : Fin R.N} {c : CfgM} {id : w64} {s s' : PState}
    (hin : InMask msk R net xnet) (h : TickEnd (R.k n) c id s s') : TickEndO (R.k n) c id s s' :=
  tickEndO_of ((hin.b1a hmsk).2.1 n) h


/-! ## Parity B1, stage B: pre-vote and check quorum (`mskB1p`)

`mskB1a` with pre-vote and check quorum on (RawNode features and node flags) and each node's
`StepDownOnRemoval`. A received message's step is the reading `RecvEndO` or one of the new arms
(`RecvEndP`: the stale answers, the lease, the pre-vote request and response); a tick's is `TickEndO`
or a pre-campaign or a check-quorum step-down (`TickEndP`); `Advance`'s is `AdvanceEndO` of the
self-acknowledgements and self-votes, or of a pre-candidate's self pre-votes nothing or the campaign
(`advanceEnd_pre`). -/

/-- **Parity B1, stage B (pre-vote, check quorum)**. -/
def mskB1p : SimMask :=
  { md := { prevote := true, cq := true, nonVoters := true },
    k := { prevote := true, cq := true, sdr := true }, campaign := true }

/-- A mask below `mskB1a` is below `mskB1p`. -/
theorem SimMask.le_b1p {msk : SimMask} (h : msk ≤ mskB1a) : msk ≤ mskB1p := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, ⟨k1, k2, k3⟩, c1, c2, c3, c4, c5, c6⟩ := h
  refine ⟨⟨?_, ?_, a3, a4, a5, a6, a7, a8, a9⟩, ⟨?_, ?_, ?_⟩, c1, c2, c3, c4, c5, c6⟩ <;>
    intro _ <;> rfl

/-- Below `mskB1p`, the mask admits only recv, tick, propose and campaign. -/
theorem Input.inMask_b1p {msk : SimMask} (hmsk : msk ≤ mskB1p) {inp : Input} (h : inp.InMask msk) :
    (∃ m, inp = .recv m) ∨ inp = .tick ∨ (∃ d, inp = .propose d) ∨ inp = .campaign := by
  obtain ⟨⟨_, _, h3, h4, _, h6, h7, h8, _⟩, _, _, h12, _⟩ := hmsk
  cases inp <;> simp_all [Input.InMask, BLe, mskB1p]

/-- The types of `mskB1p`'s network: the S4 types, the pre-vote request and response. -/
def B1pTy (t : MsgType) : Prop := S4Ty t ∨ t = .preVote ∨ t = .preVoteResp

/-- Below `mskB1p`, the run has pre-vote, check quorum and non-voters at most, no driver mode, and
its network only `B1pTy`. -/
theorem InMask.b1p {msk : SimMask} (hmsk : msk ≤ mskB1p) {R : RunCfg} {net : List Msg}
    {xnet : List XMsg} (h : InMask msk R net xnet) :
    R.md = { prevote := R.md.prevote, cq := R.md.cq, nonVoters := R.md.nonVoters } ∧
    R.drv.batch = false ∧ R.drv.parallel = false ∧ R.drv.split = 0 ∧ R.drv.restarts = false ∧
    xnet = [] ∧ ∀ m ∈ net, B1pTy m.ty := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, ⟨k1, k2, k3⟩, c1, c2, c3, c4, c5, c6⟩ := hmsk
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩, hk, d1, d2, d3, d4, hnet, hx⟩ := h
  simp only [BLe, mskB1p] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hR : R.md; simp_all
  · cases h : R.drv.batch <;> simp_all
  · cases h : R.drv.parallel <;> simp_all
  · cases h : R.drv.split with
    | zero => rfl
    | succ _ => exact absurd (d3 (by simp [h])) (by simp_all)
  · cases h : R.drv.restarts <;> simp_all
  · cases h : msk.md.transfer <;> simp_all
  · intro m hm; rcases hnet m hm with h | h
    · simp only [NetTy] at h
      rcases h with h | h | h | h | h | h | ⟨-, h | h⟩ | ⟨hp, _⟩ | ⟨hp, _⟩ <;> simp_all [B1pTy, S4Ty]
    · simp [B1pTy, S4Ty, h]

/-- `RawNode.Campaign` is a tick's campaign or pre-campaign step (whatever the node's pre-vote). -/
theorem tickEndR_of_campaignEndR' {k : NodeK} {id : w64} {r r' : RState}
    (h : CampaignEndR k id r r') : TickEndR k id r r' := by
  obtain ⟨h0 | ⟨hnl, -, -, ⟨hk, hce⟩ | ⟨hk', hpc⟩⟩, hkc, hfp, hsn, hpci⟩ := h
  · subst h0; exact ⟨.inl rfl, hkc, hfp, hsn, hpci⟩
  · exact ⟨.inr (.inl ⟨hnl, hk, hce⟩), hkc, hfp, hsn, hpci⟩
  · exact ⟨.inr (.inr (.inl ⟨hnl, hk', hpc⟩)), hkc, hfp, hsn, hpci⟩

/-- **An input below `mskB1p`**: a message received, a proposal, or a tick's step (a tick, or
`Campaign`: `tickEndR_of_campaignEndR'`). -/
theorem Input.step_b1p {msk : SimMask} (hmsk : msk ≤ mskB1p) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {n : Fin R.N}
    {r r₁ : RState} {inp : Input}
    (h : inp.InMask msk) (hs : InputStep R dec Adm n r inp r₁) :
    (∃ m, inp = .recv m) ∨ ((inp = .tick ∨ inp = .campaign) ∧ InputStep R dec Adm n r .tick r₁) ∨
      ∃ d, inp = .propose d := by
  rcases Input.inMask_b1p hmsk h with ⟨m, rfl⟩ | rfl | ⟨d, rfl⟩ | rfl
  · exact .inl ⟨m, rfl⟩
  · exact .inr (.inl ⟨.inl rfl, hs⟩)
  · exact .inr (.inr ⟨d, rfl⟩)
  · exact .inr (.inl ⟨.inr rfl, tickEndR_of_campaignEndR' hs⟩)

/-- **`RecvEnd`'s pre-vote and check-quorum arms** (beyond `RecvEndO`): a stale `MsgApp` or
`MsgHeartbeat` answered by an empty `MsgAppResp` at the node's term (check quorum or pre-vote on);
a stale pre-vote request rejected at the node's term; a vote or pre-vote request ignored in the
lease; a pre-vote request answered (`PreVoteEndP`, the term kept); a rejected pre-vote response of
a higher term making a follower with no leader at its term; any other pre-vote response nothing,
or on a grant at a follower with no leader the campaign (`CampaignSends`, the election's requests
with no context). -/
def RecvEndP (k : NodeK) (c : CfgM) (id : w64) (s : PState) (m : Msg) (s' : PState) : Prop :=
  (uint.Z m.term < uint.Z s.term ∧ (k.cq = true ∨ k.prevote = true) ∧ (m.ty = .app ∨ m.ty = .heartbeat) ∧
    s' = psendMsgs s [Msg.mk .appResp id m.src s.term false (W64 0) (W64 0) (W64 0) (W64 0) []]) ∨
  (uint.Z m.term < uint.Z s.term ∧ m.ty = .preVote ∧
    s' = psendMsgs s [Msg.plain .preVoteResp id m.src s.term true]) ∨
  (LeaseIgnore k s m ∧ s' = s) ∨
  (m.ty = .preVote ∧ PreVoteEndP id s m s') ∨
  (m.ty = .preVoteResp ∧ m.reject = true ∧ uint.Z s.term < uint.Z m.term ∧
    s' = pbecomeFollower s m.term (W64 0)) ∨
  (m.ty = .preVoteResp ∧
    (s' = s ∨ (s.role = .follower ∧ s.lead = W64 0 ∧ m.reject = false ∧ CampaignSends c id s [] s')))

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

/-- **`RecvEnd` below `mskB1p`** (a `B1pTy` type, no context on a heartbeat response, no deferred
read request) is the reading `RecvEndO` or a new arm (`RecvEndP`). -/
theorem recvEnd_split {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hty : B1pTy m.ty) (hctx : m.ty = .heartbeatResp → m.ctx = []) (hp : s.rd.pend = [])
    (h : RecvEnd k c id s m s') :
    (RecvEndO k c id s m s' ∧ (S4Ty m.ty ∨ s' = s)) ∨ RecvEndP k c id s m s' := by
  rcases hty with hty | hpv | hpr
  · rcases h with ⟨h0, hh⟩ | ⟨h0, hlt, hst⟩ | ⟨-, hli, rfl⟩ | ⟨h0, s1, hpre, hh⟩
    · exact .inl ⟨.inl ⟨h0, handleEndO_of hty hctx hp hh⟩, .inl hty⟩
    · rcases hst with rfl | ⟨hc, happ, rfl⟩ | ⟨hpv, -⟩
      · exact .inl ⟨.inr (.inl ⟨h0, hlt, rfl⟩), .inl hty⟩
      · exact .inr (.inl ⟨hlt, hc, happ, rfl⟩)
      · rcases hty with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at hpv <;> cases hpv
    · exact .inr (.inr (.inr (.inl ⟨hli, rfl⟩)))
    · exact .inl ⟨.inr (.inr ⟨h0, s1, preEndO_of hty hpre,
        handleEndO_of hty hctx ((preEnd_pend hpre).trans hp) hh⟩), .inl hty⟩
  · have hpre_s : ∀ {s1 : PState}, PreEnd k s m s1 → s1 = s := by
      intro s1 hpre
      rcases hpre with ⟨-, hk, -⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact absurd (.inl hpv) hk
      · rfl
      · rfl
    have hhd : ∀ {s1 : PState}, HandleEnd k c id s1 m s' → PreVoteEndP id s1 m s' := by
      intro s1 hh; simp only [HandleEnd, hpv] at hh; exact hh
    rcases h with ⟨-, hh⟩ | ⟨h0, hlt, hst⟩ | ⟨-, hli, rfl⟩ | ⟨-, s1, hpre, hh⟩
    · exact .inr (.inr (.inr (.inr (.inl ⟨hpv, hhd hh⟩))))
    · rcases hst with rfl | ⟨-, happ, -⟩ | ⟨-, rfl⟩
      · exact .inl ⟨.inr (.inl ⟨h0, hlt, rfl⟩), .inr rfl⟩
      · rw [hpv] at happ; rcases happ with h' | h' <;> cases h'
      · exact .inr (.inr (.inl ⟨hlt, hpv, rfl⟩))
    · exact .inr (.inr (.inr (.inl ⟨hli, rfl⟩)))
    · rw [hpre_s hpre] at hh
      exact .inr (.inr (.inr (.inr (.inl ⟨hpv, hhd hh⟩))))
  · rcases h with ⟨-, hh⟩ | ⟨h0, hlt, hst⟩ | ⟨-, hli, rfl⟩ | ⟨-, s1, hpre, hh⟩
    · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨hpr, handleEnd_preVoteResp hpr hh⟩)))))
    · rcases hst with rfl | ⟨-, happ, -⟩ | ⟨hpv, -⟩
      · exact .inl ⟨.inr (.inl ⟨h0, hlt, rfl⟩), .inr rfl⟩
      · rw [hpr] at happ; rcases happ with h' | h' <;> cases h'
      · rw [hpr] at hpv; cases hpv
    · obtain ⟨-, h1 | h1, -⟩ := hli <;> rw [hpr] at h1 <;> cases h1
    · rcases hpre with ⟨hlt, hk, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · have hrj : m.reject = true := by
          cases h : m.reject
          · exact absurd (.inr ⟨hpr, h⟩) hk
          · rfl
        have hfl : fromLeader m.ty = false := by rw [hpr]; rfl
        simp only [hfl, Bool.false_eq_true, if_false] at hh
        rcases handleEnd_preVoteResp hpr hh with h' | ⟨-, -, h', -⟩
        · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨hpr, hrj, hlt, h'⟩)))))
        · rw [hrj] at h'; cases h'
      · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨hpr, handleEnd_preVoteResp hpr hh⟩)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨hpr, handleEnd_preVoteResp hpr hh⟩)))))

/-- **`TickEnd`'s pre-vote and check-quorum arms** (beyond `TickEndO`): a pre-campaign at a
non-leader, a leader's check-quorum step-down to a follower with no leader at its term. -/
def TickEndP (k : NodeK) (c : CfgM) (id : w64) (s s' : PState) : Prop :=
  (s.role ≠ .leader ∧ k.prevote = true ∧ PreCampaignEnd c id s s') ∨
  (s.role = .leader ∧ k.cq = true ∧ s' = pbecomeFollower s s.term (W64 0))

/-- **`TickEnd`** is the reading `TickEndO` or a new arm (`TickEndP`). -/
theorem tickEnd_split {k : NodeK} {c : CfgM} {id : w64} {s s' : PState}
    (h : TickEnd k c id s s') : TickEndO k c id s s' ∨ TickEndP k c id s s' := by
  rcases h with h | ⟨hnl, -, hid, peers, hperm, heq⟩ | ⟨hnl, hk, hpc⟩ | h4 | ⟨hl, hk, h5⟩
  · exact .inl (.inl h)
  · exact .inl (.inr (.inl ⟨hnl, hid, peers, [], hperm, heq⟩))
  · exact .inr (.inl ⟨hnl, hk, hpc⟩)
  · exact .inl (.inr (.inr h4))
  · exact .inr (.inr ⟨hl, hk, h5⟩)

/-- `RecvEnd` of a self-acknowledgement or a self-vote (whatever the node's flags: no stale answer,
no lease for these types) is the reading. -/
theorem recvEndO_of_resp {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hq : m.ty = .appResp ∨ m.ty = .voteResp) (hp : s.rd.pend = []) (h : RecvEnd k c id s m s') :
    RecvEndO k c id s m s' := by
  have hty : S4Ty m.ty := by rcases hq with h | h <;> simp [S4Ty, h]
  rcases recvEnd_split (.inl hty) (fun h => by rcases hq with h' | h' <;> rw [h'] at h <;> cases h) hp h
    with h | h
  · exact h.1
  · exfalso
    rcases h with ⟨-, -, h1 | h1, -⟩ | ⟨-, h1, -⟩ | ⟨⟨-, h1 | h1, -⟩, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      rcases hq with h' | h' <;> rw [h'] at h1 <;> cases h1

/-- **`AdvanceEnd` of self-acknowledgements and self-votes** (whatever the node's flags) is its
reading. -/
theorem advanceEndO_of' {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp) (hp : s.rd.pend = [])
    (h : AdvanceEnd k c id s qs s') : AdvanceEndO k c id s qs s' := by
  induction h with
  | nil s => exact .nil s
  | cons s s1 s' q qs hr _ ih =>
    have hq0 := hq q List.mem_cons_self
    have hr' := recvEndO_of_resp hq0 hp hr
    exact .cons _ _ _ q qs hr'
      (ih (fun q' hq' => hq q' (List.mem_cons_of_mem _ hq')) ((recvEndO_pend_self hq0 hr').trans hp))

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

/-! ## `Advance` and `Reach` read on the protocol state below `mskB1p` -/

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

/-- **`Advance` of a view's queue** (`QsOk`, homogeneous): of self-acknowledgements and self-votes,
the reading `AdvanceEndO`; of a pre-candidate's self pre-votes (a voter's, pre-vote on), nothing or
the campaign at a follower with no leader (`advanceEnd_pre`). -/
theorem AdvanceEnd.split {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {k : NodeK}
    {c : CfgM} {s' : PState} (hqs : ∀ q ∈ v.qs, QsOk R S n v q) (hp : v.ps.rd.pend = [])
    (h : AdvanceEnd k c (nodeId n) v.ps v.qs s') :
    (AdvanceEndO k c (nodeId n) v.ps v.qs s' ∧ ∀ q ∈ v.qs, q.ty ≠ .preVoteResp) ∨
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
  · have hno : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp := fun q hq hty => hex ⟨q, hq, hty⟩
    refine .inl ⟨advanceEndO_of' (fun q hq => ?_) hp h, hno⟩
    exact ((hqs q hq).notPre (hno q hq)).2.2.2.2.imp (fun h => h.1) (fun h => h.1)

/-- The `by` of a drain whose input steps as a tick (`TickEnd`): a tick, or `Campaign`
(`tickEndR_of_campaignEndR'`). -/
def TickBy (b : AntCheck.Str) : Prop := b = go!"tick" ∨ b = go!"campaign"

/-- **`Reach` read on the protocol state** (below `mskB1p`: the inputs a message received, a tick
or a proposal, the configuration `c` fixed): no input; a received message (sent to the node, of a
nonzero term) of an S4 type stepped as the reading (`RecvEndO`) or a pre-vote/check-quorum arm (`RecvEndP`; a
granted pre-vote response to a voter); a tick stepped as the reading (`TickEndO`) or a pre-campaign
or check-quorum step-down (`TickEndP`); a proposal (`ProposeEnd`); `Advance` stepping the queued
self-acknowledgements and self-votes (`AdvanceEndO`), or a voter's queued self pre-votes: nothing or
the campaign (`AdvanceEnd.split`). -/
inductive ReachP (kk : NodeK) (c : CfgM) (id : w64) (net : List Msg) : NodeView → PState → Prop
  | stay (v : NodeView) : v.Idle → ReachP kk c id net v v.ps
  | recv (v : NodeView) (m : Msg) (ps₁ : PState) : v.Idle → v.byE = go!"recv" → v.cause = some m →
      m ∈ net → m.dst = id → m.term ≠ W64 0 → S4Ty m.ty → RecvEndO kk c id v.ps m ps₁ →
      ReachP kk c id net v ps₁
  | recvP (v : NodeView) (m : Msg) (ps₁ : PState) : v.Idle → v.byE = go!"recv" → v.cause = some m →
      m ∈ net → m.dst = id → m.term ≠ W64 0 → (m.ty = .preVoteResp → m.reject = false → id ∈ c.voters) →
      RecvEndP kk c id v.ps m ps₁ → ReachP kk c id net v ps₁
  | tick (v : NodeView) (ps₁ : PState) : v.Idle → TickBy v.byE → TickEndO kk c id v.ps ps₁ →
      ReachP kk c id net v ps₁
  | tickP (v : NodeView) (ps₁ : PState) : v.Idle → TickBy v.byE → TickEndP kk c id v.ps ps₁ →
      ReachP kk c id net v ps₁
  | propose (v : NodeView) (d : List w8) (ps₁ : PState) : v.Idle → v.byE = go!"propose" →
      ProposeEnd c id v.ps (propMsg id d) ps₁ → ReachP kk c id net v ps₁
  | advance (v : NodeView) (ps₁ : PState) : v.pend = [] → v.ce = [] → DrainBy v.byE →
      (∀ q ∈ v.qs, q.ty ≠ .preVoteResp) → AdvanceEndO kk c id v.ps v.qs ps₁ → ReachP kk c id net v ps₁
  | advP (v : NodeView) (ps₁ : PState) : v.pend = [] → v.ce = [] → DrainBy v.byE →
      (∀ q ∈ v.qs, q.ty = .preVoteResp ∧ q.reject = false) → id ∈ c.voters → kk.prevote = true →
      (ps₁ = v.ps ∨ (v.ps.role = .follower ∧ v.ps.lead = W64 0 ∧ CampaignSends c id v.ps [] ps₁)) →
      ReachP kk c id net v ps₁

/-- A proposal's step is the reading (no new arm reads a proposal). -/
theorem recvEndO_of_prop {k : NodeK} {c : CfgM} {id : w64} {s s' : PState} {d : List w8}
    (hp : s.rd.pend = []) (h : RecvEnd k c id s (propMsg id d) s') :
    RecvEndO k c id s (propMsg id d) s' := by
  rcases recvEnd_split (.inl (by simp [S4Ty, propMsg])) (fun h => by simp [propMsg] at h) hp h
    with h | h
  · exact h.1
  · exfalso
    rcases h with ⟨-, -, h1 | h1, -⟩ | ⟨-, h1, -⟩ | ⟨⟨-, h1 | h1, -⟩, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      simp [propMsg] at h1

/-- **`ReachIn` below `mskB1p` is its protocol reading** at the node's configuration. -/
theorem ReachIn.toP {msk : SimMask} (hmsk : msk ≤ mskB1p) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {net : List Msg} {xnet : List XMsg} {n : Fin R.N}
    {S : AntCheck.State} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) : ReachP (R.k n) v.r.cfg.cfg (nodeId n) net v r₁.p := by
  obtain ⟨hmd, -, -, -, -, -, hty⟩ := hin.b1p hmsk
  have hrd : R.md.reads = false := by rw [hmd]
  have hcc : R.md.confChanges = false := by rw [hmd]
  have hp := hv.facts.pend0 hrd
  cases hr with
  | stay hi => exact .stay _ hi
  | input inp _ hinp hi hbe hca _ hm _ hs =>
    rcases Input.step_b1p hmsk hinp hs with ⟨m, rfl⟩ | ⟨hti, hs⟩ | ⟨d, rfl⟩
    · obtain ⟨hmn, hmd', hm0⟩ := hm m rfl
      rcases recvEnd_split (hty m hmn) (fun h1 => (hnet.2.2.2.2.1 m hmn).2.2.2 hrd (.inr h1)) hp hs.1
        with ⟨h, h4 | he⟩ | h
      · exact .recv _ m _ hi hbe hca hmn hmd' hm0 h4 h
      · rw [he]; exact .stay _ hi
      · refine .recvP _ m _ hi hbe hca hmn hmd' hm0 (fun h1 h2 => ?_) h
        have := ((hnet.2.2.2.2.2 m hmn) hcc).2 h1 h2
        rw [(hv.facts.conf0 hcc).1, CfgM.voters_simple, ← hmd']; exact this
    · have hti' : TickBy v.byE := by rcases hti with rfl | rfl <;> simp [hbe, Input.byE, TickBy]
      rcases tickEnd_split hs.1 with h | h
      · exact .tick _ _ hi hti' h
      · exact .tickP _ _ hi hti' h
    · rcases recvEndO_of_prop hp hs.1 with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact .propose _ d _ hi hbe hh
      · exact absurd rfl h0
      · exact absurd rfl h0
  | advance _ hpd _ hce _ hb ha _ =>
    rcases AdvanceEnd.split hv.qs hp (advanceEndR_toP ha) with ⟨h, hno⟩ | ⟨hpr, hvt, hpv, h⟩
    · exact .advance _ _ hpd hce hb hno h
    · exact .advP _ _ hpd hce hb hpr hvt hpv h

end inputs

end AntSim
end EtcdGrove
end Perennial
