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
    (net : List Msg) (xnet : List XMsg) (n : Fin R.N) : NodeView → RState → List XMsg → Prop
  | stay (v : NodeView) : v.Idle → ReachIn msk R dec Adm net xnet n v v.r []
  | input (v : NodeView) (inp : Input) (r₁ : RState) (xs : List XMsg) :
      inp.InMask msk →
      v.Idle → v.byE = inp.byE → v.cause = inp.cause → v.xcause = inp.xcause →
      (∀ m, inp = .recv m → m ∈ net ∧ m.dst = nodeId n ∧ m.term ≠ W64 0) →
      (∀ x, inp = .recvX x → x ∈ xnet ∧ x.dst = nodeId n) →
      InputStep R dec Adm n v.r inp r₁ xs → ReachIn msk R dec Adm net xnet n v r₁ xs
  | advance (v : NodeView) (r₁ : RState) :
      v.pend = [] → v.xpend = [] → v.ce = [] → v.rpend = [] → DrainBy v.byE →
      AdvanceEndR Adm dec (R.k n) (nodeId n) v.r v.qs r₁ →
      (R.md.snapshots = false → AdvanceNoSnap Adm dec (R.k n) (nodeId n) v.r v.qs r₁) →
      ReachIn msk R dec Adm net xnet n v r₁ []

/-- `Quiet` with the input admitted by the mask. -/
inductive QuietIn (msk : SimMask) (R : RunCfg) (dec : CCDec) (Adm : List EntryM → CCState → Prop)
    (net : List Msg) (xnet : List XMsg) (n : Fin R.N) : NodeView → NodeView → Prop
  | input (v : NodeView) (inp : Input) :
      inp.InMask msk →
      v.Idle → (∀ m, inp = .recv m → m ∈ net ∧ m.dst = nodeId n) →
      (∀ x, inp = .recvX x → x ∈ xnet ∧ x.dst = nodeId n) →
      QuietIn msk R dec Adm net xnet n v (v.noteInput inp)
  | noReady (v : NodeView) (r₁ : RState) :
      ReachIn msk R dec Adm net xnet n v r₁ [] → r₁.p.outbox = [] → r₁.p.rd.states = [] →
      r₁.p.term = v.ps.term → r₁.p.vote = v.ps.vote → r₁.p.commit = v.ps.commit →
      r₁.p.role = v.ps.role → r₁.full = v.r.full →
      QuietIn msk R dec Adm net xnet n v { v with r := r₁, qs := [] }
  | silentReady (v : NodeView) (r₁ : RState) (xs : List XMsg) (rd : ReadyD) :
      ReachIn msk R dec Adm net xnet n v r₁ xs → ReadyOutP R n v r₁ xs rd → ¬ Reported v rd →
      QuietIn msk R dec Adm net xnet n v (v.drainOf r₁ rd)

theorem ReachIn.reach {msk : SimMask} {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : NodeView} {r₁ : RState} {xs : List XMsg}
    (h : ReachIn msk R dec Adm net xnet n v r₁ xs) : Reach R dec Adm net xnet n v r₁ xs := by
  cases h with
  | stay h1 => exact .stay _ h1
  | input inp _ _ h0 h1 h2 h3 h4 h5 h6 h7 => exact .input _ inp _ _ h1 h2 h3 h4 h5 h6 h7
  | advance _ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

theorem Input.inMask_top [GooseExts] (inp : Input) : inp.InMask mskTop := by
  cases inp <;> simp [Input.InMask, mskTop]

theorem ReachIn.ofReach_top {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : NodeView} {r₁ : RState} {xs : List XMsg}
    (h : Reach R dec Adm net xnet n v r₁ xs) : ReachIn mskTop R dec Adm net xnet n v r₁ xs := by
  cases h with
  | stay h1 => exact .stay _ h1
  | input inp _ _ h1 h2 h3 h4 h5 h6 h7 => exact .input _ inp _ _ (Input.inMask_top inp) h1 h2 h3 h4 h5 h6 h7
  | advance _ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

theorem QuietIn.ofQuiet_top {R : RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v v' : NodeView}
    (h : Quiet R dec Adm net xnet n v v') : QuietIn mskTop R dec Adm net xnet n v v' := by
  cases h with
  | input inp h1 h2 h3 => exact .input _ inp (Input.inMask_top inp) h1 h2 h3
  | noReady _ h1 h2 h3 h4 h5 h6 h7 h8 => exact .noReady _ _ (ReachIn.ofReach_top h1) h2 h3 h4 h5 h6 h7 h8
  | silentReady _ _ _ h1 h2 h3 => exact .silentReady _ _ _ _ (ReachIn.ofReach_top h1) h2 h3

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
    {r r₁ : RState} {xs : List XMsg} {inp : Input} (hin : AntSim.InMask msk R net xnet)
    (h : inp.InMask msk) (hs : InputStep R dec Adm n r inp r₁ xs) :
    (∃ m, inp = .recv m) ∨ ((inp = .tick ∨ inp = .campaign) ∧ InputStep R dec Adm n r .tick r₁ xs) ∨
      ∃ d, inp = .propose d := by
  rcases Input.inMask_b1a hmsk h with ⟨m, rfl⟩ | rfl | ⟨d, rfl⟩ | rfl
  · exact .inl ⟨m, rfl⟩
  · exact .inr (.inl ⟨.inl rfl, hs⟩)
  · exact .inr (.inr ⟨d, rfl⟩)
  · exact .inr (.inl ⟨.inr rfl, tickEndR_of_campaignEndR (by rw [(hin.b1a hmsk).2.1 n]) hs.1, hs.2⟩)

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
  exact recvEndO_of (hk n) (hty m hm) (fun h1 => (hnet.2.2.2.2 m hm).2.2.2 hrd (.inr h1))
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

end inputs

end AntSim
end EtcdGrove
end Perennial
