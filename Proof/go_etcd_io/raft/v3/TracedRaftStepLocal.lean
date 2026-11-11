/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on the local paths that log lines**
(2026-11-10, trace-check Q8 stage 1 slice 18a, `notes/decisions.md`, "Q8 stage 1 (slice 18a)"): proofs of
`stepBundle_traced.on Path` (`TracedRaftStep.lean`) for the local messages a traced node steps at a role
where they log lines.

**`MsgBeat` at a leader** (`LocalBeat`, `stepBundle_traced_beat`): `bcastHeartbeat`, one heartbeat per
peer, each a `SendAppendEntriesRequest` line (`"#Hgbeat"`). The caller's resources are one family
(`lineF`: raft's ghost state, the traced family at the idle server of `s`, the new messages' numbers)
from the receive gate (no line: `lineF_recv`) to the close; each heartbeat's gate pins the share
(`trCapB_pinMem`), fires the line by `trCapB_hookGateOpt` (its phase step `phaseStepB_heartbeat_pin`,
its facts `fxPres_heartbeat_pin`, its numbers from the receipts' bound, `ownRaftGhost_traceBound`) and
unpins (`trFam_unpin`); the close reads `StepEnd`'s `LeaderNonpropResultC` (the heartbeats queued, the
`Match` values unchanged) and re-orders the share (`lineF_close`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedPin
public import Spec.go_etcd_io.raft.v3.raft__tickHeartbeat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A heartbeat's or an append's destination, a peer of the tracker, is a voter of the incoming half (no
learners, no outgoing half). -/
theorem mem_incoming_of (c : CfgM) (to : w64) (hl : c.learners = ∅) (hout : c.outgoing = ∅)
    (h : to ∈ c.voters ∪ c.learners) : to ∈ elements c.incoming := by
  rw [elem_of_elements]
  rw [hl, CfgM.voters, hout, GMap.union_empty_r_L, GMap.union_empty_r_L] at h
  exact h

/-- The idle server's part does not read the `Progress` values beyond their `Match` values. -/
theorem simIdleS_prvals (C : List w64) (s : NState) (ms : List Msg) (pvs : GMap w64 Progress)
    (h : prvalsMatch pvs = prvalsMatch s.prvals) :
    SimIdleS C { sendMsgs s ms with prvals := pvs } = SimIdleS C s := by
  have : toPState { sendMsgs s ms with prvals := pvs } = toPState (sendMsgs s ms) := by
    simp only [toPState, h]; rfl
  unfold SimIdleS
  rw [this]
  rfl

/-- **`MsgBeat` at a leader** (the heartbeats). -/
def LocalBeat (s : NState) (m : MessageM) : Prop := m.Type' = MsgBeat ∧ s.role = .leader

/-- A heartbeat's numbers (`Msg.TrOk`): the leader's term and a commit at most its own. -/
theorem heartbeat_trOk (id to tm cm : w64) (cl : List w8) (ht : uint.nat tm < traceNumBound)
    (hc : uint.nat cm < traceNumBound) :
    (Msg.mkV .heartbeat id to tm false (W64 0) (W64 0) cm (W64 0) [] [] cl).TrOk := by
  intro _
  have h0 : uint.nat (W64 0) = 0 := rfl
  have hb : (0 : Nat) < traceNumBound := by unfold traceNumBound; omega
  refine ⟨ht, ?_, ?_, ?_, hc, ?_⟩ <;> simp only [List.length_nil, h0] <;> exact hb

end pure

section gates
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `HookGateOpt` under an update. -/
theorem hookGateOpt_fupd (tr : Option GName) (r : Loc) (oE : Option (TraceEv → Prop)) (Q : IProp GF) :
    iprop(|={⊤}=> HookGateOpt tr r oE Q) ⊢ HookGateOpt tr r oE Q := by
  iintro H
  iunfold HookGateOpt at H
  iunfold HookGateOpt
  imod H with H
  iexact H

/-- **The node's numbers from raft's ghost state** (`ownRaftGhost_traceBound`): its commit and last
indices below the trace's bound, under an update. -/
theorem ownStepGhost_traceBound (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      |==> (⌜uint.nat s.logst.committed < traceNumBound ∧ uint.nat (plastIndex (toPState s)) < traceNumBound⌝ ∗
        ownStepGhost γ md c id s) := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  imod ownRaftGhost_traceBound (GF := GF) γ id (toPState s) hfit $$ Hg with ⟨%Hb, Hg⟩
  imodintro
  iunfold ownStepGhost
  iframe Hg Hr
  ipureintro
  obtain ⟨h1, h2⟩ := Hb
  have h0 : (0 : Int) ≤ plogLastIndexZ (toPState s).base (toPState s).log := by
    unfold plogLastIndexZ; have := uint_Z_nonneg (toPState s).base.index'; omega
  have hb : traceNumBound = 2 ^ 61 := rfl
  constructor
  · simp only [toPState] at h2; word
  · unfold plastIndex; rw [hb] at h1 ⊢; word

/-- **A leader's heartbeat's gate on a local path's family** (`leaderGates`' `"#Hgbeat"`): the share
pinned, the `SendAppendEntriesRequest` line fired (`trCapB_hookGateOpt`: `phaseStepB_heartbeat_pin`,
`fxPres_heartbeat_pin`), the share unpinned at the outbox with the heartbeat. -/
theorem lineF_heartbeat (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Λ : Option TraceEv → Prop) (to cm : w64) (cl : List w8) (o : List Msg)
    (htr : s.gh.tr = some γd) (hlead : s.role = .leader) (hne : to ≠ id)
    (hdom : to ∈ c.voters ∪ c.learners) (hlrn : c.learners = ∅)
    (hcm : uint.Z cm = min (uint.Z s.logst.committed) (uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0))))
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    lineF (GF := GF) γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) o ⊢
      HookGateOpt s.gh.tr r
        (sendOutGate id s c MsgHeartbeat [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl])
        (lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ)
          (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl])) := by
  unfold lineF trFam
  rw [htr, sendOutGate_one id s c MsgHeartbeat _ (W64 9) rfl]
  iintro ⟨Hgh, ⟨%bt, Hf⟩, %Hok⟩
  iapply hookGateOpt_fupd
  imod ownStepGhost_traceBound (GF := GF) γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
  icases trCapB_out γd γ r id c bt _ _ $$ Hf with ⟨%Hout, Hf⟩
  icases trCapB_pinMem γd γ r id c bt _ _ $$ Hf with ⟨%C0, %cs0, %P0, %HΦ0, Hf⟩
  icases trCapB_logger γd γ r id c bt _ _ $$ Hf with ⟨%tl, #Htl, Hf⟩
  obtain ⟨ma0, hma⟩ : ∃ ma0, TraceSim.msgAbs C0 C0.length
      (Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl) = some ma0 := ⟨_, rfl⟩
  have hto := mem_incoming_of c to hlrn Hout hdom
  have hcmle : uint.Z cm ≤ uint.Z s.logst.committed := by rw [hcm]; exact Int.min_le_left _ _
  have hTn : uint.nat s.term < traceNumBound := by word
  have hcn : uint.nat cm < traceNumBound := by have := Hb.1; word
  ihave #Hfx := fxPres_heartbeat_pin (GF := GF) γ id
    (SendEvOf (W64 9) id s c (Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl))
    s o to cm cl C0 cs0 P0 ma0 hma HΦ0.2 hlead hcmle
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  imodintro
  iapply hookGateOpt_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true (PinAt s C0 cs0 (P0 ++ [ma0])
      (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl])) (stepLastEv Λ) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun _ _ _ h => h.2.2.2) $$ Hc
    ipureintro
    exact outOk_snoc Hok (heartbeat_trOk id to s.term cm cl hTn hcn)
  iapply trCapB_hookGateOpt (some γd) γ r id c tl _ bt (PinAt s C0 cs0 P0 o) _ (stepLastEv Λ) (stepLastEv Λ)
    iprop(emp) (phaseStepB_heartbeat_pin id c s o to cm cl C0 cs0 P0 ma0 hma hlead hne hto hcm)
    (fun e he => sendEvOf_notBoot he (by decide) (by decide) (by decide))
    (fun e _ => .inr rfl)
    (fun _ e he => sendEvOf_ok (W64 9) id s c _ e _ he (by decide) hTn Hb.1 Hb.2
      (heartbeat_trOk id to s.term cm cl hTn hcn rfl) (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hf Hfx

/-- `MsgBeat` is none of the other types `Step` switches on (decided on the constants). -/
theorem msgBeat_ne :
    MsgBeat ≠ MsgProp ∧
    MsgBeat ≠ MsgReadIndex ∧
    MsgBeat ≠ MsgTransferLeader ∧
    MsgBeat ≠ MsgCheckQuorum ∧
    MsgBeat ≠ MsgHeartbeatResp ∧
    MsgBeat ≠ MsgAppResp ∧
    MsgBeat ≠ MsgHup ∧
    MsgBeat ≠ MsgVote ∧
    MsgBeat ≠ MsgPreVote ∧
    MsgBeat ≠ MsgVoteResp ∧
    MsgBeat ≠ MsgApp ∧
    MsgBeat ≠ MsgHeartbeat ∧
    MsgBeat ≠ MsgReadIndexResp ∧
    MsgBeat ≠ MsgForgetLeader ∧
    MsgBeat ≠ MsgTimeoutNow ∧
    MsgBeat ≠ MsgUnreachable ∧
    MsgBeat ≠ MsgSnapStatus ∧
    MsgBeat ≠ MsgPreVoteResp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [MsgBeat, MsgProp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgReadIndex, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgTransferLeader, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgCheckQuorum, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgHeartbeatResp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgAppResp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgHup, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgVote, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgPreVote, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgVoteResp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgApp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgHeartbeat, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgReadIndexResp, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgForgetLeader, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgTimeoutNow, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgUnreachable, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgSnapStatus, ne_eq]; exact of_decide_eq_true rfl
  · simp only [MsgBeat, MsgPreVoteResp, ne_eq]; exact of_decide_eq_true rfl

/-- `LocalBeat`'s resources: one family (`lineF` at the idle server of `s`) wherever `Step` may end,
`False` between hooks no path here reaches. -/
def beatR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Λ : Option TraceEv → Prop) : StepG GF where
  G := trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ
  G0 := lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ)
  G1 := lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ)
  GE := lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ)
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ)
  Gc := fun _ _ => lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ)

/-- The end state of a `LocalBeat` path (`StepEnd`, traced): the heartbeats queued, the `Match` values
unchanged. -/
theorem localBeat_end {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hp : LocalBeat s m) (hns : ¬ StaleMsg s m) (hpre : ∀ pvs, preState s m pvs = s)
    (h : StepEnd c id m ents ctx s s') :
    ∃ (ms : List Msg) (pvs : GMap w64 Progress), s' = { sendMsgs s ms with prvals := pvs } ∧
      prvalsMatch pvs = prvalsMatch s.prvals := by
  have hty : StepEndTy m.Type' := by unfold StepEndTy; simp [hp.1]
  have hnh : m.Type' ≠ MsgHup := by rw [hp.1]; exact msgBeat_ne.2.2.2.2.2.2.1
  have hnv : m.Type' ≠ MsgVote := by rw [hp.1]; exact msgBeat_ne.2.2.2.2.2.2.2.1
  obtain ⟨pvs, hfn⟩ := (h hty).2.2.2 hns hnh hnv
  rw [hpre pvs] at hfn
  obtain ⟨d, hres⟩ := hfn.2.2 hp.2
  unfold LeaderStepResultC at hres
  have nP : m.Type' ≠ MsgProp := by rw [hp.1]; exact msgBeat_ne.1
  rw [if_neg nP] at hres
  obtain ⟨-, hres⟩ := hres
  have hb := msgBeat_ne
  rcases hres with ⟨ht, -⟩ | ⟨-, ms, pvs', hs', -, hm⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
  · exfalso; rw [hp.1] at ht; simp only [hb, _root_.or_false] at ht
  · exact ⟨ms, pvs', hs', hm⟩
  all_goals exfalso; rw [hp.1] at ht; simp only [hb, _root_.or_false] at ht

/-- **`raft.Step`'s traced bundle on `MsgBeat` at a leader** (the heartbeats). -/
theorem stepBundle_traced_beat : stepBundle_traced.on (GF := GF) (hG := hG) LocalBeat := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hsub _ _ _
  have hT0 : m.Term' = W64 0 := hloc (.inr (.inl hp.1))
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h; have := h.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => h.1 hT0
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have nP : m.Type' ≠ MsgProp := by rw [hp.1]; exact msgBeat_ne.1
  have nRI : m.Type' ≠ MsgReadIndex := by rw [hp.1]; exact msgBeat_ne.2.1
  have nTL : m.Type' ≠ MsgTransferLeader := by rw [hp.1]; exact msgBeat_ne.2.2.1
  have nCQ : m.Type' ≠ MsgCheckQuorum := by rw [hp.1]; exact msgBeat_ne.2.2.2.1
  have nHR : m.Type' ≠ MsgHeartbeatResp := by rw [hp.1]; exact msgBeat_ne.2.2.2.2.1
  have nAR : m.Type' ≠ MsgAppResp := by rw [hp.1]; exact msgBeat_ne.2.2.2.2.2.1
  have nH : m.Type' ≠ MsgHup := by rw [hp.1]; exact msgBeat_ne.2.2.2.2.2.2.1
  have nV : m.Type' ≠ MsgVote := by rw [hp.1]; exact msgBeat_ne.2.2.2.2.2.2.2.1
  have nPV : m.Type' ≠ MsgPreVote := by rw [hp.1]; exact msgBeat_ne.2.2.2.2.2.2.2.2.1
  iintro ⟨Hcap, -, #Hnosnap⟩
  imodintro
  iexists beatR bt γ md c r id s Λ
  isplitl [Hcap]
  · dsimp only [beatR]; iexact Hcap
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, beatR]
    isplitr
    · -- the receive hook: no line for `MsgBeat`
      iintro ⟨Hgh, Hc⟩
      have hrg : recvGate id s c ⟨m, ents, sn, ctx, rs⟩ = none := by
        apply recvGate_none_of
        intro ty hty'
        have hm1 : mtypeOf MsgBeat = none := rfl
        simp only [hp.1, hm1] at hty'; cases hty'
      rw [hrg]
      iapply lineF_recv γd γ md c r id s Λ bt htr
      iframe Hgh Hc
    isplitr
    · unfold preGate
      iintro %_ HG0
      rw [if_neg hnbf]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (h.1 hT0).elim
    isplitr
    · iintro %h
      exact (h.elim nV nPV).elim
    isplitr
    · iintro %h; exact (nH h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      dsimp only
      isplit
      · iintro %hr; rw [hp.2] at hr; cases hr
      isplit
      · iintro %hr; rcases hr with hr | hr <;> rw [hp.2] at hr <;> cases hr
      · iintro %_
        unfold leaderGates
        isplitr
        · -- the heartbeats
          imodintro
          iintro %_ %to %cm %o %Hto %Hcm HG
          iapply lineF_heartbeat γd γ md c r id s Λ to cm (hbCtx s.rd.ro) o htr hp.2 Hto.1
            ((GMap.elem_of_subseteq _ _).1 hsub _ Hto.2) hlrn Hcm hT hfit
          iexact HG
        isplitr
        · iintro %h; exact (nRI h).elim
        isplitr
        · imodintro; iintro %h; exact (nRI h).elim
        isplitr
        · iintro %h; exact (nTL h).elim
        isplitr
        · iintro %h; exact (nTL h).elim
        isplitr
        · iexact Hnosnap
        isplitr
        · iintro %h; exact (nCQ h).elim
        isplitr
        · iintro %h; exact (nP h).elim
        isplitr
        · iintro %h; exact (nP h).elim
        isplitr
        · imodintro; iintro %h; exact (nP h).elim
        isplitr
        · iintro %h; exact (h.elim nHR (fun h => nAR h.1)).elim
        isplitr
        · imodintro; iintro %h; exact (nHR h).elim
        isplitr
        · iintro %h; exact (nAR h.1).elim
        isplitr
        · imodintro; iintro %h; exact (nAR h.1).elim
        isplitr
        · imodintro; iintro %h; exact (nAR h.1).elim
        isplitr
        · imodintro; iintro %h; exact (nAR h.1).elim
        · imodintro; iintro %h; exact (nAR h.1).elim
    · ipureintro
      exact ⟨lineF_permInv γ md c r id s _ _, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: the heartbeats queued, the `Match` values unchanged; the share re-ordered
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_ne nP)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨ms, pvs, rfl, hm⟩ := localBeat_end hp hns hpre (hend (by rw [htr]; rfl))
    have hS : ∀ C, SimIdleS C s = SimIdleS C { sendMsgs s ms with prvals := pvs } :=
      fun C => (simIdleS_prvals C s ms pvs hm).symm
    ihave H : lineF (GF := GF) γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ)
      ({ sendMsgs s ms with prvals := pvs } : NState).outbox $$ [Hout]
    · unfold stepOut
      dsimp only [beatR]
      icases Hout with (H | H | H | H | ⟨%b, %N, H⟩) <;> iexact H
    iapply lineF_close γ md c r id s _ (stepLastEv Λ) hS $$ H

/-- A local message's token: nothing (an untraced type; `recvTokOf` asks only of a traced one). -/
theorem recvTokOf_untraced (γd : GName) (m : MessageM) (ents : List EntryM) (ctx : List w8)
    (h : mtypeOf m.Type' = none) : ⊢ recvTokOf (GF := GF) γd m ents ctx := by
  iunfold recvTokOf
  iintro %ty %hty
  rw [h] at hty
  exact absurd hty.1 (by simp)

/-- **`raft.tickHeartbeat` at a traced leader** (check-quorum off, so no quorum check): the capability
idle at `s` in, idle at the end state out (`stepBundle_traced_beat` for the heartbeat's `Step`; with no
heartbeat the capability as it was, the end state's server part `s`'s). What a traced node API supplies:
the capability and `TrNoSnap`, pre-vote and check-quorum off, the term's and the receipts' bounds, no
learners. (2026-11-11, slice 22a, Q19) The capability with any `booted` flag in, some flag out (a tick
may come before the node's first `Ready` line). -/
abbrev raft.tickHeartbeat.tracedTriple : Prop :=
  ∀ (c : CfgM) (md : GMode) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (γd : GName)
    (Λ : Option TraceEv → Prop) (bt : Bool),
  NStateWf s → md.Guard s →
  s.gh.tr = some γd → s.prevote = false → s.cq = false →
  uint.Z s.term + 1 < traceNumBound → receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  c.learners = ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s ∗
      "Hcap" ∷ trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ ∗
      "#Hnosnap" ∷ TrNoSnap s.gh.tr s.logst }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"tickHeartbeat")) (Val #()))
  {{ (s' : NState), RET #();
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md c id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      "%Hcm" ∷ ⌜uint.Z s.logst.committed ≤ uint.Z s'.logst.committed ∧
        PVoteLe (toPState s) (toPState s')⌝ ∗
      "%Htick" ∷ ⌜TickStep s s'⌝ ∗
      "Hcap" ∷ ∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ) }}

/-- `raft.tickHeartbeat.spec`'s traced instance (see `raft.tickHeartbeat.tracedTriple`). -/
theorem raft.tickHeartbeat.traced (h : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.tickHeartbeat.tracedTriple (GF := GF) (hG := hG) := by
  intro c md γ r id s γd Λ bt Hwf Hpc htr hpv hcq hT hfit hlrn
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hcap, #Hnosnap⟩ HΦ
  icases ownRaftPhysC_dom c r id s $$ Hphys with ⟨%Hsub, Hphys⟩
  iapply h c md γ r id s (beatR bt γ md c r id s Λ)
    (fun s1 => iprop(⌜s1 = s⌝ ∗ trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ))
    (fun s' => iprop(∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ))) Hwf Hpc
    $$ [Hphys Hghost Hcap]
  · iframe Hinit Hphys Hghost
    isplitl [Hcap]
    · dsimp only [beatR]; iexact Hcap
    isplitr
    · iintro %h; rw [hcq] at h; cases h
    isplitr
    · iintro HG
      imodintro
      isplitr
      · ipureintro; rfl
      dsimp only [beatR]; iexact HG
    iintro %s1 %s2 %Hs2 ⟨%Hs1, Hc⟩
    subst s1
    obtain ⟨hgh, hrole, hs2⟩ := Hs2
    have hsame : s2.gh = s.gh ∧ s2.prevote = s.prevote ∧ s2.cq = s.cq ∧ s2.term = s.term ∧
        s2.logst = s.logst ∧ s2.progress = s.progress ∧ (NStateWf s2 ↔ NStateWf s) ∧
        (fun C => SimIdle C s2) = (fun C => SimIdle C s) := by
      rcases hs2 with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Iff.rfl, rfl⟩
    obtain ⟨_, hpv2, hcq2, hT2, hls2, hpr2, hwf2, hS2⟩ := hsame
    have htr2 : s2.gh.tr = some γd := by rw [hgh]; exact htr
    have hb : (tickMsg MsgBeat id).Type' = MsgBeat := rfl
    have hmt : mtypeOf (tickMsg MsgBeat id).Type' = none := rfl
    ihave Htok := recvTokOf_untraced (GF := GF) γd (tickMsg MsgBeat id) [] [] hmt
    have hgo := stepBundle_traced_beat (GF := GF) (hG := hG) γ md c r id s2 (tickMsg MsgBeat id) [] none [] []
      γd Λ bt ⟨hb, hrole⟩ htr2 (hpv2.trans hpv) (hcq2.trans hcq) (by unfold StepEndTy; simp)
      (hwf2.2 Hwf) (fun _ => rfl) (fun h => absurd (h.symm.trans hb) (by
        simp only [MsgHup, MsgBeat]; exact of_decide_eq_true rfl))
      (fun ty h => by rw [hmt] at h; cases h) (by rw [hT2]; exact hT) (by simp; unfold traceNumBound; omega)
      (fun ty h => by rw [hmt] at h; cases h) hfit hlrn (by rw [hpr2]; exact Hsub) (by rw [hrole]; nofun)
      (by refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [hb] at h <;>
            simp [MsgBeat, MsgHeartbeat, MsgHeartbeatResp, MsgVote, MsgApp] at h)
      (fun h => by rw [hb] at h; simp [MsgBeat, MsgHeartbeat, MsgApp] at h)
    rw [hS2, hgh, hls2] at hgo
    iapply hgo
    iframe Hc Htok Hnosnap
    imodintro; iintro %ty %h; rw [hmt] at h; exact absurd h.1 (by simp)
  inext
  iintro %s' H
  iapply HΦ $$ %s'
  iNamed H
  iframe Hphys Hghost
  isplitr
  · ipureintro; exact Hwf'
  isplitr
  · ipureintro; exact Hcm
  isplitr
  · ipureintro; exact Htick
  icases HG with (⟨%s1, %Hs', %Hs1, Hc⟩ | Hc)
  · subst s1
    have hS : (fun C => SimIdle C s') = (fun C => SimIdle C s) := by
      rcases Hs' with rfl | rfl <;> rfl
    rw [hS]
    iexists bt
    iapply trCapB_monoΛ s.gh.tr γ r id c bt _ Λ (stepLastEv Λ) (fun o h => .inl h) $$ Hc
  · iexact Hc

end gates

end EtcdGrove
end Perennial
