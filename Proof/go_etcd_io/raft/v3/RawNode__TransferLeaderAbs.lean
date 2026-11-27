/-
Antithesis parity B1, phase 2 (#33, `notes/antithesis-parity-design.md` §4). **`RawNode.TransferLeader`,
the strengthened triple** (`RawNode.TransferLeader.absSpec`, `RawNodeAbsSpecs.lean`). The proof is
`RawNode__TransferLeader.lean`'s, over `ownRawNodeAt` at a mode `md` with transfer, without snapshots or
configuration changes: the message `pb.Message{Type: MsgTransferLeader, From: to}` built as before, then
`raft.Step` at the no-snapshot flag (`raft.Step.untracedNs`). Its end state (`StepEnd.xfer`, at the state
with the transfer's ghost records) is the start state but for the ghost state, the transferee, the outbox
and `Progress` values of the same `Match` (`transferEnd_of_stepEnd`): a follower or candidate keeps the
protocol state (a forward is untyped), a leader appends to the transferee, a voter other than itself
(`TransferEndR`). The scope's transfer facts (`XScopeOk`) from `%Hxwframe`'s growth conjunct: the one
record a step adds is a follower's forward to its known leader.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__TransferLeader
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
public import Proof.go_etcd_io.raft.v3.LemmasP3bXw
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.TracedUntracedRaftStep
public import Proof.go_etcd_io.raft.v3.RaftStepNoSnap
public import Proof.go_etcd_io.raft.v3.RawNodeAtScope
public import Proof.go_etcd_io.raft.v3.RawNodeReadyAt
public import Proof.go_etcd_io.raft.v3.StepEndIp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgRest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess



section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- `m.Type' = MsgTransferLeader` (`hty`) refutes a hypothesis `h` about another type. -/
local macro "tl_absurd" : tactic => `(tactic| (rw [hty] at h; simp [MsgUnreachable, MsgHup, MsgBeat,
  MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgSnap, MsgHeartbeat, MsgHeartbeatResp,
  MsgSnapStatus, MsgCheckQuorum, MsgTransferLeader, MsgTimeoutNow, MsgReadIndex, MsgReadIndexResp,
  MsgPreVote, MsgPreVoteResp, MsgStorageAppendResp, MsgStorageApplyResp, MsgForgetLeader] at h))

set_option maxHeartbeats 1000000 in
/-- **The end state of a `MsgTransferLeader` the preamble keeps** (`StepEnd.xfer`: not stale, no
step-down; a local one, term `0`, or (antithesis parity B1, step B) a forwarded one of the node's term):
`s` but for the ghost state, the transferee `lt`, the outbox and `Progress` values of the same `Match`;
the protocol reading kept, or (a leader) the appends `SendsEnd` to the transferee `m.From'`, a voter
other than the node. `hpc`: the progress map tracks the configuration's ids (`ownRaftPhysC_trkDoms`);
`hns`: no `MsgSnap` queued (`raft.Step.untracedNs`). -/
theorem transferEnd_of_stepEnd_cur {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hty : m.Type' = MsgTransferLeader) (hst : ¬ StaleMsg s m)
    (hnb : ¬ PreBF m s)
    (hpc : domSet s.progress = c.ids) (hns : NoSnapL s'.outbox) (h : StepEnd c id m ents ctx s s') :
    ∃ (g : NGhost) (l : w64) (o : List Msg) (pvs : GMap w64 Progress),
      s' = { s with gh := g, lt := l, outbox := o, prvals := pvs } ∧
      prvalsMatch pvs = prvalsMatch s.prvals ∧
      (toPState s' = toPState s ∨
        (s.role = .leader ∧ m.From' ∈ c.voters ∧ m.From' ≠ id ∧
          SendsEnd c id (toPState s) (toPState s'))) := by
  have hnh : m.Type' ≠ MsgHup := fun h => by tl_absurd
  have hnp : m.Type' ≠ MsgProp := fun h => by tl_absurd
  obtain ⟨X, Y, b, pvs0, hfn⟩ := h.xfer hst hty
  rw [ie_preState_nobf (s := { s with gh := { s.gh with xw := X, xt := Y, xs := b } }) (fun h' => hnb h')] at hfn
  obtain ⟨hf, hc, hl⟩ := hfn
  have hkeep : s' = { s with gh := { s.gh with xw := X, xt := Y, xs := b } } →
      ∃ (g : NGhost) (l : w64) (o : List Msg) (pvs : GMap w64 Progress),
        s' = { s with gh := g, lt := l, outbox := o, prvals := pvs } ∧
        prvalsMatch pvs = prvalsMatch s.prvals ∧
        (toPState s' = toPState s ∨
          (s.role = .leader ∧ m.From' ∈ c.voters ∧ m.From' ≠ id ∧
            SendsEnd c id (toPState s) (toPState s'))) := fun he =>
    ⟨{ s.gh with xw := X, xt := Y, xs := b }, s.lt, s.outbox, s.prvals, by rw [he], rfl,
      .inl (by rw [he]; rfl)⟩
  have hroles : s.role = .follower ∨ s.role = .candidate ∨ s.role = .preCandidate ∨
      s.role = .leader := by cases s.role <;> simp
  rcases hroles with hr | hr | hr | hr
  · obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    obtain ⟨-, -, he⟩ := StepProof.followerStepResult_rnoop c id _ m ents sv d s' ctx (.inl hty) hres
    exact hkeep he
  · obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    obtain ⟨-, -, he⟩ :=
      StepProof.candidateStepResult_rest c id _ m ents sv d s' ctx (.inr (.inr (.inr (.inr hty)))) hres
    exact hkeep he
  · obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    obtain ⟨-, -, he⟩ :=
      StepProof.candidateStepResult_rest c id _ m ents sv d s' ctx (.inr (.inr (.inr (.inr hty)))) hres
    exact hkeep he
  · obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC at hres
    rw [if_neg hnp] at hres
    obtain ⟨-, hres⟩ := hres
    unfold LeaderNonpropResultC at hres
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨-, lt', ms, pvs, rfl, ⟨hrs, hx⟩, hpm, -⟩ | ⟨h, -⟩
    rotate_right 2
    · have hP : toPState { sendMsgs { { s with gh := { s.gh with xw := X, xt := Y, xs := b } } with
            lt := lt' } ms with prvals := pvs } = psendMsgs (toPState s) ms :=
        ie_toPState_send_prvals _ ms pvs (fun _ => hpm)
      refine ⟨{ s.gh with xw := X, xt := Y, xs := b }, lt', s.outbox ++ ms, pvs, rfl, hpm, ?_⟩
      by_cases hms : ms = []
      · subst hms
        left
        rw [hP]
        simp [psendMsgs]
      · obtain ⟨hv, hni⟩ := hx hty hms
        refine .inr ⟨hr, hv, hni, ms, fun y hy => ?_, hP⟩
        have hn : y.ty ≠ .snap := hns y (List.mem_append_right _ hy)
        exact ⟨(hrs y hy).1.app hn, (hrs y hy).2.1, ie_dst_ids rfl hpc (hrs y hy).2.2.1⟩
    all_goals exfalso
    all_goals tl_absurd

/-- **The end state of a local `MsgTransferLeader`** (term `0`): `transferEnd_of_stepEnd_cur`. -/
theorem transferEnd_of_stepEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hty : m.Type' = MsgTransferLeader) (hT0 : m.Term' = W64 0)
    (hpc : domSet s.progress = c.ids) (hns : NoSnapL s'.outbox) (h : StepEnd c id m ents ctx s s') :
    ∃ (g : NGhost) (l : w64) (o : List Msg) (pvs : GMap w64 Progress),
      s' = { s with gh := g, lt := l, outbox := o, prvals := pvs } ∧
      prvalsMatch pvs = prvalsMatch s.prvals ∧
      (toPState s' = toPState s ∨
        (s.role = .leader ∧ m.From' ∈ c.voters ∧ m.From' ≠ id ∧
          SendsEnd c id (toPState s) (toPState s'))) :=
  transferEnd_of_stepEnd_cur hty (fun h' => h'.1 hT0)
    (fun h' => by have := h'.1; rw [hT0] at this; simp at this) hpc hns h

set_option maxHeartbeats 1000000 in
/-- (antithesis parity B1, step B) **A received `MsgTransferLeader` of a higher term** (`StepEnd.xfer`,
the preamble's step-down): the node a follower at the message's term with no leader
(`becomeFollower(m.Term, None)`), which drops it (`stepFollower`). -/
theorem transferEnd_of_stepEnd_gt {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hty : m.Type' = MsgTransferLeader) (hst : ¬ StaleMsg s m)
    (hb : PreBF m s) (h : StepEnd c id m ents ctx s s') :
    ∃ (g : NGhost) (pvs : GMap w64 Progress),
      s' = { becomeFollower { s with gh := g } m.Term' (W64 0) with prvals := pvs } := by
  obtain ⟨X, Y, b, pvs0, hfn⟩ := h.xfer hst hty
  have hb' : PreBF m { s with gh := { s.gh with xw := X, xt := Y, xs := b } } := hb
  have hpl : preLead m = W64 0 := by
    unfold preLead
    rw [if_neg (by rw [hty]; simp [MsgApp, MsgHeartbeat, MsgSnap, MsgTransferLeader])]
  simp only [preState, hb', ↓reduceIte, hpl] at hfn
  obtain ⟨hf, -, -⟩ := hfn
  obtain ⟨scfg, sv, d, c', hres⟩ := hf (by simp [becomeFollower])
  obtain ⟨-, -, he⟩ := StepProof.followerStepResult_rnoop c id _ m ents sv d s' ctx (.inl hty) hres
  exact ⟨_, pvs0, he⟩

/-- (antithesis parity B1, step B) `TransferRecvEndR`'s higher-term arm at the `RState` reading. -/
theorem transferRecvEndR_of_gt {rs : RNState} {fp : List EntryM} {id : w64} {s : NState} {x : XMsg}
    {g : NGhost} {pvs : GMap w64 Progress} (hgt : uint.Z s.term < uint.Z x.term) :
    TransferRecvEndR id (toRState rs fp s) x
      (toRState rs fp { becomeFollower { s with gh := g } x.term (W64 0) with prvals := pvs }) := by
  refine .inr (.inr ⟨hgt, ?_⟩)
  have hp : toPState { becomeFollower { s with gh := g } x.term (W64 0) with prvals := pvs } =
      pbecomeFollower (toPState s) x.term (W64 0) := by
    rw [toPState_prvals_nl _ _ (by simp [becomeFollower]), toPState_becomeFollower]; rfl
  simp only [toRState, hp]
  simp [pciR, becomeFollower, resetTo, resetTo0]

/-- `TransferEndR` at the `RState` reading, from `transferEnd_of_stepEnd`'s conclusion. -/
theorem transferEndR_of {rs : RNState} {fp : List EntryM} {c : CfgM} {id to : w64} {s : NState}
    {g : NGhost} {l : w64} {o : List Msg} {pvs : GMap w64 Progress} (hc : rs.cfg.cfg = c)
    (hp : toPState { s with gh := g, lt := l, outbox := o, prvals := pvs } = toPState s ∨
      (s.role = .leader ∧ to ∈ c.voters ∧ to ≠ id ∧
        SendsEnd c id (toPState s) (toPState { s with gh := g, lt := l, outbox := o, prvals := pvs }))) :
    TransferEndR id (toRState rs fp s) to
      (toRState rs fp { s with gh := g, lt := l, outbox := o, prvals := pvs }) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rcases hp with hp | ⟨hr, hv, hni, hse⟩
  · exact .inl hp
  · subst hc
    refine .inr ⟨?_, hv, hni, hse⟩
    show proleRole s.role = .leader
    rw [hr]; rfl


/-- (antithesis parity B1, phase 2) **A stale received `MsgTransferLeader`** (`StepEnd.xstale`): ignored, but
for the transfer's ghost record, which `toRState` does not read: `TransferRecvEndR`'s first arm. -/
theorem transferRecvEndR_of_stale {rs : RNState} {fp : List EntryM} {c : CfgM} {id : w64} {m : MessageM}
    {ents : List EntryM} {ctx : List w8} {s s' : NState} {x : XMsg} (hty : m.Type' = MsgTransferLeader)
    (hst : StaleMsg s m) (hxt : x.term = m.Term') (h : StepEnd c id m ents ctx s s') :
    TransferRecvEndR id (toRState rs fp s) x (toRState rs fp s') := by
  obtain ⟨X, Y, b, rfl⟩ := h.xstale hst hty
  exact .inl ⟨by rw [hxt]; exact hst.1, by rw [hxt]; exact hst.2, rfl⟩

set_option maxHeartbeats 1000000 in
/-- (antithesis parity B1, phase 2) **A received `MsgTransferLeader`** (`x` its transfer reading: the
sender `x.src`, the term `x.term`), `TransferRecvEndR` at the `RState` reading: stale
(`transferRecvEndR_of_stale`), of a higher term (`transferEnd_of_stepEnd_gt`), else of the node's term or
term `0` (`transferEnd_of_stepEnd_cur`, `transferEndR_of`). -/
theorem transferRecvEndR_of_stepEnd {rs : RNState} {fp : List EntryM} {c : CfgM} {id : w64}
    {m : MessageM} {ents : List EntryM} {ctx : List w8} {s s' : NState} {x : XMsg}
    (hc : rs.cfg.cfg = c) (hty : m.Type' = MsgTransferLeader) (hpc : domSet s.progress = c.ids)
    (hns : NoSnapL s'.outbox) (hxs : x.src = m.From') (hxt : x.term = m.Term')
    (h : StepEnd c id m ents ctx s s') :
    TransferRecvEndR id (toRState rs fp s) x (toRState rs fp s') := by
  by_cases hst : StaleMsg s m
  · exact transferRecvEndR_of_stale hty hst hxt h
  by_cases hb : PreBF m s
  · obtain ⟨g, pvs, rfl⟩ := transferEnd_of_stepEnd_gt hty hst hb h
    rw [← hxt]
    exact transferRecvEndR_of_gt (by rw [hxt]; exact hb.1)
  · obtain ⟨g, l, o, pvs, rfl, -, hp⟩ := transferEnd_of_stepEnd_cur hty hst hb hpc hns h
    refine .inr (.inl ⟨?_, ?_⟩)
    · rw [hxt]
      by_cases h0 : m.Term' = W64 0
      · exact .inl h0
      · right
        have h1 : ¬ uint.Z m.Term' < uint.Z s.term := fun h' => hst ⟨h0, h'⟩
        have h2 : ¬ uint.Z s.term < uint.Z m.Term' := fun h' => hb ⟨h', fun h => by tl_absurd,
          fun ⟨h, _⟩ => by tl_absurd⟩
        show m.Term' = s.term
        word
    · rw [hxs]; exact transferEndR_of hc hp

/-- A premise of `Step` about another message type. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow,
  MsgTransferLeader] at Hc))

set_option maxHeartbeats 2000000 in
/-- **`RawNode.TransferLeader`, strengthened** (`RawNode.TransferLeader.absSpec`). -/
theorem RawNode.TransferLeader.wp_absProof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.TransferLeader.absSpec (GF := GF) (hG := hG) := by
  have wp_raft_StepNs := raft.Step.untracedNs wp_raft_Step
  intro md hsn hcc γ rn id rs ps qs ip transferee htr HtrG
  have htrf : md.transfer = true := htr md rfl
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the scope at `md`: no snapshot, and without configuration changes no automatic leave
  icases rnScopeAt_someMd md rs s $$ Hsc with ⟨%Hscp, #Hcap0, Hsc⟩
  ihave #Hcap := Hcap0 $$ %hsn
  obtain ⟨Hrsc, Hcin, -, Hxs⟩ := Hscp
  obtain ⟨-, Hprev, -, Hnsq⟩ := Hrsc.2.2.2.2.1 hsn
  icases ownRaftPhysC_ackScope cf rnv.raft' id s $$ Hphys with ⟨%Hal0, Hphys⟩
  icases ownStepGhost_cfgScope γ rs fp _ cf id s $$ Hghost with ⟨%Hcfm, Hghost⟩
  icases ownRaftPhysC_trkDoms cf rnv.raft' id s $$ Hphys with ⟨%Htd, Hphys⟩
  have Hcfe : rs.cfg.cfg = cf := Hcfm.2 Hcin.2.2.2
  have Hal : AckScope cf := by
    have ho := Hrsc.1 hcc Hcin.2.2.2
    rw [Hcfe] at ho
    exact Hal0 ho
  have Hp0 : uint.Z s.logst.prev.index' = 0 := by rw [Hprev]; rfl
  wp_auto_lc 1
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 13) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v1» with #cFr
  imod msgOwnZ_lit0 true «$a0_ptr» _ ({ (zero_val MessageM) with Type' := W32 13, From' := transferee } : MessageM) ⊤ $$ [«$a0»] with Hm
  · iframe «$a0» cTy cFr
    isplitr
    · ipureintro; simp
    msg_nulls
  -- (out_size C3) a literal without entries or context: at a content of bounded size
  ihave Hm := msgOwnZ_to_msgInC _ _ _ (by simp [MsgApp]) $$ Hm
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  wp_apply wp_raft_StepNs cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 13, From' := transferee } : MessageM) [] [] none []
    (by simp [StepMsg, stepMsgTypes, MsgTransferLeader])
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (⟨fun h => absurd h (by msg_ne), fun h => absurd h (by msg_ne), fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ : RestMsgOk s _ [] []) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    (by tr_none) Hal $$ [$Hphys $Hghost $Hlc1 Hcr Hm]
  · -- the message: no entries, no `Context`, no snapshot
    have hP : (W32 13 : w32) ≠ MsgProp := by simp [MsgProp]
    simp only [hP, ↓reduceIte, named]
    -- unstamped (term `0`): no transfer witness needed
    isplitr
    · imodintro
      iintro %h
      exact (h.2 rfl).elim
    isplitl [Hm]
    · isplitl [Hm]
      · iapply msgInC_flag true _ (fun _ => rfl) _ _ _ $$ Hm
      repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
      imodintro
      iintro %ty %Hty
      rw [show mtypeOf (W32 13) = none from rfl] at Hty
      cases Hty
    isplitl [Hcr]
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr
    isplitr
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
    isplitr
    · iexact Hcap
    isplitr
    · ipureintro; exact Hp0
    · ipureintro; exact Hnsq
  have hP : (W32 13 : w32) ≠ MsgProp := by simp [MsgProp]
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, -, %Hxwf, %Htm, -, -, -, Herr,
    %Hend, -, %Hns', -⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
  have e2 := Hcc (by msg_ne); subst c'
  wp_auto
  -- the forward may record `(lead, term)` in `xw` (`"%Hxwframe"`): `NetFrame` at the ghost state
  -- before the step, which the step changes only in `xw`, `xt`, `xs`
  obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, -, Hfl', Hap'⟩, Hgx, -, Hgrow⟩ := Hxwf (.inl rfl)
  simp only at Ha Hsn Hu Hpv Hsd Hsg Hpre Hfl' Hap'
  -- the end state: `s` but for the ghost state, the transferee, the outbox, the `Progress` values
  obtain ⟨g, l, o, pvs, Hse, Hpm, Hpe⟩ := transferEnd_of_stepEnd (s := s) (s' := s') rfl rfl Htd.2 Hns' Hend
  icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
  have Hsneq : s'.gh.sn = s.gh.sn := by rw [Hgx]
  have Htceq : s'.gh.tc = s.gh.tc := by rw [Hgx]
  obtain ⟨Ht1, -, -, Hip4, -, Hpcs⟩ := Htm (by msg_ne)
  have Htrm' : rs.term = s'.term := by rw [Htrm, Hse]
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 (by msg_ne)) $$ Hstrecs
  -- the scope at `md` kept (transfer on: the ghost records may grow, by a follower's forward to its
  -- known leader, a member of the configuration)
  ihave Hsc := rnScopeAt_keepSomeX md rs rs s s'
    (fun Hs => by
      obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9⟩ := Hs
      rw [Hse]
      exact ⟨h1, h2, h3, h4, fun hs => by
        obtain ⟨h51, h52, h53, -⟩ := h5 hs
        exact ⟨h51, h52, h53, by rw [← Hse]; exact Hns'⟩,
        fun h => absurd (htrf.symm.trans h) (by decide), h7, h8,
        fun a b c => mem_domSet_of_prvalsMatch Hpm (h9 a b c)⟩)
    (by rw [Hse]) (hfl := by rw [Hse]; exact ⟨rfl, rfl, rfl⟩)
    (hx := fun _ Hx => by
      obtain ⟨hl, hw, ht⟩ := Hx
      have hlead : (toPState s').lead = (toPState s).lead := by rw [Hse]; rfl
      have hterm : s'.term = s.term := by rw [Hse]
      refine ⟨(fun hnv => by rw [hlead]; exact hl hnv), fun p hp => ?_, by rw [hlead, hterm]; exact ht⟩
      rcases Hgrow p hp with hp' | ⟨rfl, hr, hl0⟩
      · exact hw p hp'
      · -- the forward's record: the follower's known leader, at its term (past `0`: `XScopeOk`'s last)
        have hld : (toPState s).lead = s.lead := toPState_lead_nonpre s (by rw [hr]; decide)
        refine ⟨fun hnv => ?_, ht (by rw [hld]; exact hl0)⟩
        rcases hl hnv with h | h
        · exact absurd (hld.symm.trans h) hl0
        · rw [hld] at h; exact h) $$ Hsc
  ihave Hrntr := rnTrace_none (GF := GF) γ rnv.raft' id cf rs.delivered s'
    (by rw [Hgx]; exact Hgtr.trans HtrG)
  have Hip' : uint.nat s'.logst.inprogress = ip + 1 := by rw [Hse]; exact Hip
  have HendR : TransferEndR id ps transferee (toRState rs fp s') := by
    rw [← Hps, Hse]
    exact transferEndR_of Hcfe (by rw [← Hse]; exact Hpe)
  icases Herr with (%Herr | ⟨%Hc', -⟩)
  · iapply HΦ
    simp only [named]
    isplitl
    rotate_left
    · ipureintro
      intro md'' hmd
      exact HendR
    ihave #Hhist' := restoredSnapHistory_keep γ id Hsd $$ Hhist
    ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s) (s' := s')
      (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
      (logStoreRec_ksn Hsd) (by first | exact Href.commit_mono | exact Hcv.commit | exact Hc) (by first | exact Href.snapQueue | exact Hcv.queue | exact Hcv.1.snapQueue) $$ Hledger
    ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
    iapply ownRawNodeAt_intro γ rn id rs (toRState rs fp s') qs ip (some md) s' cf fp rnv sv hprev steps Hwf' Hin
      Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (Int.le_of_eq (congrArg _ Htceq.symm)) Hstok) Htrm'
      (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hsneq, ← Hns0.2]; exact Hstor.2⟩)
      (Hpvoff.step_gxw rfl rfl Hpre Hgx (by rw [← Htrm', Htrm]; exact Hpvoff.2.2.1) Hpcs
          (by msg_ne))
      (by rw [Hgx]; exact Hrs_out) (by rw [Hgx]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
      (RNFl.keep Hrnfl Hfl' Hap' Ha) (by
          have H := Hloan.step_gxw (b := false) rs.term Hgx
            (fun _ => ⟨.inl Hsn, Hfl', logStoreRec_stored Hsd, Hu, Ha, Hc⟩) ⟨Hsn, Hc⟩
          simp only [Bool.or_false] at H
          exact H)
      (Hsdt.ofRec Hsn Hsd) Hrole
      (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hsn (.inl (Hip4 (by msg_ne)))) rfl Hip'
      (by rw [Hgx]; exact Hgtr) (by rw [Hgx]; exact Hglq)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' Hhist' Hledger' [Hdur] Hrntr Hsc
    · -- (durability stage II (i)) the step keeps `durTie`'s fields
      iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
  · exfalso; revert Hc'; msg_ne

end proof

end EtcdGrove
end Perennial
