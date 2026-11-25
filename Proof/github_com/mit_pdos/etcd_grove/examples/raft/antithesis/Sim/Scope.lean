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
(`Input.InMask`). Each migrated statement is `antSim_X_in msk (hmsk : msk ≤ mskS4)`; B1 widens it to
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

/-- Below `mskS4`, the mask admits only recv, tick and propose. -/
theorem Input.inMask_s4 {msk : SimMask} (hmsk : msk ≤ mskS4) {inp : Input} (h : inp.InMask msk) :
    (∃ m, inp = .recv m) ∨ inp = .tick ∨ ∃ d, inp = .propose d := by
  obtain ⟨⟨_, _, h3, h4, _, h6, h7, h8, _⟩, _, h11, h12, _⟩ := hmsk
  cases inp <;> simp_all [Input.InMask, BLe, mskS4]

/-- Below `mskS4`, the run has no feature, no node flag and no driver mode, and its network only
the S4 types. -/
theorem InMask.s4 {msk : SimMask} (hmsk : msk ≤ mskS4) {R : RunCfg} {net : List Msg}
    {xnet : List XMsg} (h : InMask msk R net xnet) :
    R.md = {} ∧ (∀ n, R.k n = {}) ∧ R.drv.batch = false ∧ R.drv.parallel = false ∧ R.drv.split = 0 ∧
    R.drv.restarts = false ∧ xnet = [] ∧
    ∀ m ∈ net, m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨
      m.ty = .heartbeat ∨ m.ty = .heartbeatResp ∨ m.ty = .propose := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, ⟨k1, k2, k3⟩, c1, c2, c3, c4, c5, c6⟩ := hmsk
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩, hk, d1, d2, d3, d4, hnet, hx⟩ := h
  simp only [BLe, mskS4] at *
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

end inputs

end AntSim
end EtcdGrove
end Perennial
