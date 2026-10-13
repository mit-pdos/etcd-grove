/- Port of the part of election_proof/proof_raft__Step.v (and of
postulates_raft__Step.v) that the branch modules of `Proof/raft__Step/` share.

Rocq's `STEP_POSTULATES` (`postulates_raft__Step.v`) is the module type every branch
file of `proof_raft__Step_helpers/` is a functor over; here it is the structure
`raft.Step.Postulates`, which each branch lemma takes as its first argument.

Lean notes:
* Rocq's `step_post`, `ghost_step_recv`, `finish_branch` and `finish_branch0` are in
  `proof_raft__Step.v` itself, before the dispatch; here they are in this module so
  that the dispatch and the branch modules can share them: `stepPost` (as before, in
  `Perennial.EtcdGrove`), and `StepProof.ghost_step_recv`, `StepProof.finish_branch`,
  `StepProof.finish_branch0`.
* Rocq's `w32_ne` (`defs.v`) is the tactic macro `w32_ne` below.
* Everything below works at `HeapGS HasLC.hasLC GF` with `[AllG GF]`, as
  `raft.Step.spec` does.
* The branch modules put their lemmas in `namespace StepProof` (Rocq: one functor
  module per file, `StepMsgVoteGt` etc.); the names are unique across the modules, as
  they are in Rocq (all the functors are instantiated in one file).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raft__hup
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.voteRespMsgType
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.stepCandidate
public import Spec.go_etcd_io.raft.v3.stepFollower
public import Spec.go_etcd_io.raft.v3.stepLeader
public import Spec.go_etcd_io.raft.v3.traceReceiveMessage
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.raftLog__isUpToDate
-- the storage acknowledgements (2026-10-05)
public import Spec.go_etcd_io.raft.v3.raftLog__stableTo
public import Spec.go_etcd_io.raft.v3.raft__appliedTo
public import Spec.go_etcd_io.raft.v3.raft__reduceUncommittedSize
public import Spec.go_etcd_io.raft.v3.entsSize
public import Spec.go_etcd_io.raft.v3.payloadsSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- Rocq `w32_ne`: two distinct message-type constants differ. -/
macro "w32_ne" : tactic =>
  `(tactic| (simp only [Perennial.EtcdGrove.MsgBeat, Perennial.EtcdGrove.MsgHup,
      Perennial.EtcdGrove.MsgProp, Perennial.EtcdGrove.MsgApp, Perennial.EtcdGrove.MsgAppResp,
      Perennial.EtcdGrove.MsgVote, Perennial.EtcdGrove.MsgVoteResp, Perennial.EtcdGrove.MsgSnap,
      Perennial.EtcdGrove.MsgHeartbeat, Perennial.EtcdGrove.MsgHeartbeatResp,
      Perennial.EtcdGrove.MsgPreVote, Perennial.EtcdGrove.MsgPreVoteResp,
      Perennial.EtcdGrove.MsgStorageAppendResp, Perennial.EtcdGrove.MsgStorageApplyResp,
      Perennial.EtcdGrove.MsgReadIndex, Perennial.EtcdGrove.MsgReadIndexResp,
      Perennial.EtcdGrove.MsgForgetLeader, Perennial.EtcdGrove.MsgUnreachable,
      Perennial.EtcdGrove.MsgSnapStatus, Perennial.EtcdGrove.MsgTransferLeader,
      Perennial.EtcdGrove.MsgTimeoutNow,
      ne_eq]; word))

section base
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Rocq `STEP_POSTULATES`: the callee specs the branches are proved from. -/
structure raft.Step.Postulates : Prop where
  hup : raft.hup.spec (GF := GF) (hG := hG)
  becomeFollower : raft.becomeFollower.spec (GF := GF) (hG := hG)
  voteRespMsgType : voteRespMsgType.spec (GF := GF) (hG := hG)
  send : raft.send.specS (GF := GF) (hG := hG)
  stepCandidate : stepCandidate.spec (GF := GF) (hG := hG)
  /-- A `MsgVoteResp` falls through `Step`'s type switch to `r.step(m)`, which is any
  of the three depending on the role -- on `m.Term > r.Term` the term preamble has
  already run `becomeFollower`. -/
  stepFollower : stepFollower.spec (GF := GF) (hG := hG)
  stepLeader : stepLeader.spec (GF := GF) (hG := hG)
  traceReceiveMessage : traceReceiveMessage.spec (GF := GF) (hG := hG)
  lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG)
  isUpToDate : raftLog.isUpToDate.spec (GF := GF) (hG := hG)
  -- the storage acknowledgements (2026-10-05)
  stableTo : raftLog.stableTo.spec (GF := GF) (hG := hG)
  appliedTo : raft.appliedTo.spec (GF := GF) (hG := hG)
  reduceUncommittedSize : raft.reduceUncommittedSize.spec (GF := GF) (hG := hG)
  entsSize : entsSize.spec (GF := GF) (hG := hG)
  payloadsSize : payloadsSize.spec (GF := GF) (hG := hG)

/-- What `raft.Step.spec`'s postcondition hands to `Φ`: the continuation every dispatch
lemma below ends in. `s` is the state the step starts from. -/
def stepPost (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (m : raftpb.Message) (Φ : val → IProp GF) : IProp GF :=
  iprop(∀ (err : GoInterface) (s' : NState) (ps' : PState),
    ("Hphys" ∷ ownRaftPhys cfg r id s' ∗
     "Hghost" ∷ ownRaftGhost γ id ps' ∗
     "%Hrel" ∷ ⌜NStateRel s' ps'⌝ ∗
     "%Hrefines" ∷ ⌜∃ recv, Step cfg id (toPState s) recv ps'⌝ ∗
     "%Hframe" ∷ ⌜m.Type' ≠ MsgSnap → NetFrame s s'⌝ ∗
     "%Hterm" ∷ ⌜m.Type' ≠ MsgSnap → TermStep m s s'⌝ ∗
     "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
     "Herr" ∷ (⌜err = interface.nil⌝ ∨
               (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err))) -∗ Φ #err)

namespace StepProof

/-- The frame and the term step of a branch that keeps the term and the log's fields
`NetFrame` and `TermStep` are about (each `rfl` for a state built by record updates
that do not touch them). -/
theorem keep_frame {m : raftpb.Message} {s s' : NState} (ht : s'.term = s.term)
    (ha : s'.logst.applying = s.logst.applying) (hs : s'.logst.snap = s.logst.snap)
    (hu : s'.logst.unpersisted = s.logst.unpersisted)
    (hi : s'.logst.inprogress = s.logst.inprogress)
    (hp : s'.logst.prev = s.logst.prev := by rfl)
    (hst : s'.logst.stored = s.logst.stored := by rfl)
    (hsg : s'.logst.storage = s.logst.storage := by rfl)
    (hpv : s'.prevote = s.prevote := by rfl) (hg : s'.gh = s.gh := by rfl) :
    NetFrame s s' ∧ TermStep m s s' :=
  ⟨⟨ha, hs, hu, hp, hst, hsg, hpv, hg⟩, TermStep.of_term ht (fun _ => by rw [hi]; exact Int.le_refl _)⟩

/-- The same, for a branch that keeps the whole log. -/
theorem keep_frame_logst {m : raftpb.Message} {s s' : NState} (ht : s'.term = s.term)
    (hl : s'.logst = s.logst) (hpv : s'.prevote = s.prevote := by rfl)
    (hg : s'.gh = s.gh := by rfl) :
    NetFrame s s' ∧ TermStep m s s' := by
  exact keep_frame ht (by rw [hl]) (by rw [hl]) (by rw [hl]) (by rw [hl]) (by rw [hl])
    (by rw [hl]) (by rw [hl]) hpv hg

/-- The same, for a branch that steps down to the message's term (`becomeFollower`) and
keeps the rest. -/
theorem stepdown_frame {m : raftpb.Message} {s s' : NState} (hup : m.Type' ≠ MsgHup)
    (Hle : uint.Z s.term ≤ uint.Z s'.term) (ht : s'.term = m.Term')
    (ha : s'.logst.applying = s.logst.applying) (hs : s'.logst.snap = s.logst.snap)
    (hu : s'.logst.unpersisted = s.logst.unpersisted)
    (hi : s'.logst.inprogress = s.logst.inprogress)
    (hp : s'.logst.prev = s.logst.prev := by rfl)
    (hst : s'.logst.stored = s.logst.stored := by rfl)
    (hsg : s'.logst.storage = s.logst.storage := by rfl)
    (hpv : s'.prevote = s.prevote := by rfl) (hg : s'.gh = s.gh := by rfl) :
    NetFrame s s' ∧ TermStep m s s' :=
  ⟨⟨ha, hs, hu, hp, hst, hsg, hpv, hg⟩, TermStep.of_le hup Hle (by rw [ht]; exact Int.le_refl _)
    (fun _ => by rw [hi]; exact Int.le_refl _)⟩

/-- The same, with the stepped-down state named (`s1`) and the branch's end state built
from it without touching its term or log. -/
theorem stepdown_frame' {m : raftpb.Message} {s s1 s' : NState} {l : w64}
    {pvs : GMap w64 Progress} (hup : m.Type' ≠ MsgHup) (Hgt : uint.Z s.term < uint.Z m.Term')
    (Hs1 : s1 = { becomeFollower s m.Term' l with prvals := pvs })
    (ht : s'.term = s1.term) (hl : s'.logst = s1.logst)
    (hpv : s'.prevote = s1.prevote := by rfl) (hg : s'.gh = s1.gh := by rfl) :
    NetFrame s s' ∧ TermStep m s s' := by
  subst Hs1
  exact stepdown_frame hup (by rw [ht]; exact Int.le_of_lt Hgt) (ht.trans rfl)
    (by rw [hl]; rfl) (by rw [hl]; rfl) (by rw [hl]; rfl) (by rw [hl]; rfl) (by rw [hl]; rfl)
    (by rw [hl]; rfl) (by rw [hl]; rfl) hpv hg

/-- A leader's read-only state is as the read-index code needs it (`RdOk`, 2026-10-13),
and its term is nonzero. -/
theorem ghost_rdOk (γ : RaftNames) (id : w64) (s : NState) (Hr : s.role = .leader) :
    ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗ ⌜RdOk γ.reCfg s.rd ∧ s.term ≠ W64 0⌝ := by
  iintro Hown
  have Hpr : (toPState s).role = .leader := by simp [toPState, Hr, proleRole]
  have Hrd : (toPState s).rd = s.rd := by simp [toPState, Hr]
  ihave %Hnz := ownRaftGhost_term_nz γ id (toPState s) (by rw [Hpr]; decide) $$ Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave %Hf := rdOwn_rdFacts γ id (toPState s) Hpr $$ Hrd
  rw [Hrd] at Hf
  ipureintro
  obtain ⟨H1, H2, H3⟩ := Hf
  refine ⟨⟨fun v _ => ?_, H2, H3⟩, Hnz⟩
  cases h : s.rd.ro.acks !! v with
  | none =>
    have := uint_Z_nonneg s.rd.ro.confirmed
    have h0 : uint.Z (W64 0 : w64) = 0 := by decide
    simp only [Option.getD_none]; omega
  | some a =>
    simp only [Option.getD_some]
    have := H1 v a h
    have := uint_nat_eq a
    have := uint_nat_eq s.rd.ro.confirmed
    omega

/-- A heartbeat response's context, at the leader of its term (2026-10-13): empty, or eight
bytes holding a position the queue reaches -- what `recvAck`/`maybeAdvance` need. -/
theorem ghost_hbResp_ctx (γ : RaftNames) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8) (Hr : s.role = .leader) (Hto : m.To' = id)
    (Hteq : m.Term' = s.term) :
    ⊢ ownRaftGhost (GF := GF) γ id (toPState s) -∗ isMessage γ (absMsg .heartbeatResp m ents ctx) -∗
      ⌜(ctx = [] ∨ 8 ≤ ctx.length) ∧
        (ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
                      ≤ uint.Z s.rd.ro.confirmed + (s.rd.ro.pending.length : Int))⌝ := by
  iintro Hown #Hm
  have Hpr : (toPState s).role = .leader := by simp [toPState, Hr, proleRole]
  have Hrd : (toPState s).rd = s.rd := by simp [toPState, Hr]
  unfold isMessage
  simp only [absMsg, absMsgFrom]
  icases Hm with (%H0 | ⟨%q, %recs0, %Hq, #Hlb⟩)
  · ipureintro; exact ⟨.inl H0, fun h => absurd H0 h⟩
  · obtain ⟨Hcq, Hack⟩ := Hq
    iunfold ownRaftGhost at Hown
    icases Hown with ⟨%γv, %voted, %kl, H⟩
    iNamed H
    rw [Hto, Hteq]
    ihave %Hpos := rdOwn_hbResp_pos γ id (toPState s) Hpr recs0 q Hack.1 $$ Hrd [Hlb]
    · rw [show (toPState s).term = s.term from rfl]; iexact Hlb
    rw [Hrd] at Hpos
    ipureintro
    have hl : (u64Le q).length = 8 := u64Le_length _
    refine ⟨.inr (by rw [Hcq, hl]; exact Nat.le_refl 8), fun _ => ?_⟩
    rw [Hcq, List.take_of_length_le (Nat.le_of_eq hl), u64Le_to_word]
    have := uint_nat_eq q
    have := uint_nat_eq s.rd.ro.confirmed
    omega

/-- The one ghost update of a branch: `recv` is the incoming message, some number of
times, and that message is `isMessage`. -/
theorem ghost_step_recv (γ : RaftNames) (cfg : GSet w64) (id : w64)
    (ps ps' : PState) (a : Msg) (recv : List Msg)
    (Hcfg : γ.reCfg = cfg) (Hrecv : ∀ m' ∈ recv, m' = a) (Hstep : Step cfg id ps recv ps')
    (Hna : a.ty ≠ .readIndex) :
    ⊢ isMessage (GF := GF) γ a -∗ ownRaftGhost γ id ps ={⊤}=∗ ownRaftGhost γ id ps' := by
  subst Hcfg
  iintro #Hm Hg
  have Hcnt : rdCount recv = 0 := by
    unfold rdCount; rw [List.countP_eq_zero]
    intro x hx; rw [Hrecv x hx]; simp [Hna]
  imod rdCred_zero_upd (GF := GF) γ with Hz
  ihave Hall : ([∗list] m ∈ recv, isMessage (GF := GF) γ m) $$ []
  · iapply (BigSepL.bigSepL_intro (P := iprop(□ isMessage (GF := GF) γ a))
      (fun k x hx => by
        rw [Hrecv x (List.mem_of_getElem? hx)]
        exact intuitionistically_elim))
    iexact Hm
  iapply ownRaftGhost_step γ id ps recv ps' Hstep $$ Hall [Hz] Hg
  rw [Hcnt]; iexact Hz

/-- A branch's postcondition, delivered: the ghost step, then `Φ`. -/
theorem finish_branch (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64)
    (s s' : NState) (m : raftpb.Message) (a : Msg) (recv : List Msg) (err : GoInterface)
    (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf' : NStateWf s') (Hrecv : ∀ m' ∈ recv, m' = a)
    (Hstep : Step cfg id (toPState s) recv (toPState s'))
    (Hfr : m.Type' ≠ MsgSnap → NetFrame s s') (Htm : m.Type' ≠ MsgSnap → TermStep m s s')
    (Hresp : RespStep m s s') (Hna : a.ty ≠ .readIndex := by simp [absMsg, absMsgFrom]) :
    ⊢ isMessage γ a -∗
      ownRaftGhost γ id (toPState s) -∗
      ownRaftPhys cfg r id s' -∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err)) -∗
      stepPost γ cfg r id s m Φ -∗
      |={⊤}=> Φ #err := by
  iintro #Hm Hghost Hphys Herr HΦ
  imod ghost_step_recv γ cfg id _ _ a recv Hcfg Hrecv Hstep Hna $$ Hm Hghost with Hghost
  imodintro
  unfold stepPost
  iapply HΦ $$ %err %s' %(toPState s')
  iframe Hphys Hghost Herr
  ipureintro
  exact ⟨⟨rfl, Hwf'⟩, ⟨recv, Hstep⟩, Hfr, Htm, Hresp⟩

/-- The same, for a branch that consumed nothing. -/
theorem finish_branch0 (γ : RaftNames) (cfg : GSet w64) (r : Loc) (id : w64)
    (s s' : NState) (m : raftpb.Message) (err : GoInterface) (Φ : val → IProp GF)
    (Hcfg : γ.reCfg = cfg) (Hwf' : NStateWf s')
    (Hstep : Step cfg id (toPState s) [] (toPState s'))
    (Hfr : m.Type' ≠ MsgSnap → NetFrame s s') (Htm : m.Type' ≠ MsgSnap → TermStep m s s')
    (Hresp : RespStep m s s') :
    ⊢ ownRaftGhost γ id (toPState s) -∗
      ownRaftPhys cfg r id s' -∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err)) -∗
      stepPost γ cfg r id s m Φ -∗
      |={⊤}=> Φ #err := by
  iintro Hghost Hphys Herr HΦ
  have Hst' : Step γ.reCfg id (toPState s) [] (toPState s') := by rw [Hcfg]; exact Hstep
  imod ownRaftGhost_step_0 γ id _ _ Hst' $$ Hghost with Hghost
  imodintro
  unfold stepPost
  iapply HΦ $$ %err %s' %(toPState s')
  iframe Hphys Hghost Herr
  ipureintro
  exact ⟨⟨rfl, Hwf'⟩, ⟨[], Hstep⟩, Hfr, Htm, Hresp⟩

end StepProof

end base

end EtcdGrove
end Perennial
