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
public import Proof.go_etcd_io.raft.v3.StepLemmasR
public import Proof.go_etcd_io.raft.v3.StepGhostMode
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

/-- `m.Type' ≠ MsgSnap` from a hypothesis `h` naming `m.Type'` (one type, or a disjunction of
them), for the configuration conjunct of the `stepX` results (2026-10-14, stage B7). -/
syntax "nonsnap " ident : tactic
macro_rules
  | `(tactic| nonsnap $h:ident) =>
    `(tactic| (intro hsnap; (rw [hsnap] at $h:ident); revert $h:ident; simp only [Perennial.EtcdGrove.MsgBeat,
        Perennial.EtcdGrove.MsgHup, Perennial.EtcdGrove.MsgProp, Perennial.EtcdGrove.MsgApp,
        Perennial.EtcdGrove.MsgAppResp, Perennial.EtcdGrove.MsgVote,
        Perennial.EtcdGrove.MsgVoteResp, Perennial.EtcdGrove.MsgSnap,
        Perennial.EtcdGrove.MsgHeartbeat, Perennial.EtcdGrove.MsgHeartbeatResp,
        Perennial.EtcdGrove.MsgPreVote, Perennial.EtcdGrove.MsgPreVoteResp,
        Perennial.EtcdGrove.MsgStorageAppendResp, Perennial.EtcdGrove.MsgStorageApplyResp,
        Perennial.EtcdGrove.MsgReadIndex, Perennial.EtcdGrove.MsgReadIndexResp,
        Perennial.EtcdGrove.MsgForgetLeader, Perennial.EtcdGrove.MsgUnreachable,
        Perennial.EtcdGrove.MsgSnapStatus, Perennial.EtcdGrove.MsgTransferLeader,
        Perennial.EtcdGrove.MsgTimeoutNow, _root_.or_false, _root_.false_or,
        _root_.or_self]; word))

/-- `RFrame s s'` (`StepLemmasR.lean`) for a branch's end state `s'` built from `s` by record
updates and the code's transition functions (2026-10-14, stage B7). -/
macro "rframe" : tactic =>
  `(tactic| first
    | exact Perennial.EtcdGrove.RFrame.refl _
    | (refine ⟨?_, ?_, ?_⟩ <;>
        first
        | rfl
        | (intro hrf; exact ⟨by assumption, rfl⟩)
        | (intro hrf
           simp_all [Perennial.EtcdGrove.becomeFollower, Perennial.EtcdGrove.becomeCandidate,
             Perennial.EtcdGrove.becomePrecandidate, Perennial.EtcdGrove.sendMsgs,
             Perennial.EtcdGrove.resetTo, Perennial.EtcdGrove.resetTo0,
             Perennial.EtcdGrove.heartbeatResult, Perennial.EtcdGrove.addReadState,
             Perennial.EtcdGrove.arriveState, Perennial.EtcdGrove.releasedState]
           done)
        | (simp [Perennial.EtcdGrove.becomeFollower, Perennial.EtcdGrove.becomeCandidate,
             Perennial.EtcdGrove.becomePrecandidate, Perennial.EtcdGrove.sendMsgs,
             Perennial.EtcdGrove.resetTo, Perennial.EtcdGrove.resetTo0,
             Perennial.EtcdGrove.heartbeatResult, Perennial.EtcdGrove.addReadState,
             Perennial.EtcdGrove.arriveState, Perennial.EtcdGrove.releasedState]; done)))

section cfg_eq
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- Off a `MsgSnap`, `stepFollower` leaves the configuration. -/
theorem FollowerStepResultC.cfg {c : CfgM} {scfg : CSLists} {id : w64} {s : NState}
    {m : MessageM} {ents : List EntryM} {sv : SnapshotM} {dropped : Bool}
    {s' : NState} {c' : CfgM} {cl : List w8} (h : m.Type' ≠ MsgSnap)
    (H : FollowerStepResultC c scfg id s m ents sv dropped s' c' cl) : c' = c := by
  have := H.1; rwa [ite_eq_right h] at this

/-- Off a `MsgSnap`, `stepCandidate` leaves the configuration. -/
theorem CandidateStepResultC.cfg {c : CfgM} {scfg : CSLists} {id : w64} {s : NState}
    {m : MessageM} {ents : List EntryM} {sv : SnapshotM} {dropped : Bool}
    {s' : NState} {c' : CfgM} {cl : List w8} (h : m.Type' ≠ MsgSnap)
    (H : CandidateStepResultC c scfg id s m ents sv dropped s' c' cl) : c' = c := by
  have := H.1; rwa [ite_eq_right h] at this

end cfg_eq

example [FfiSyntax] (m : MessageM)
    (Hty : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp) :
    m.Type' ≠ MsgSnap := by nonsnap Hty
example [FfiSyntax] (m : MessageM) (Hty : m.Type' = MsgHeartbeat) :
    m.Type' ≠ MsgSnap := by nonsnap Hty

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
  send : raft.send.spec (GF := GF) (hG := hG)
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
lemma below ends in. `s` is the state the step starts from, `c` its configuration
(2026-10-14, reconfiguration stage B7: the struct at `c`, the configuration afterwards `c'`
`c` but after a `MsgSnap`; the ghost state in the mode `md`, afterwards in `md'`, the step in
the mode's model, `GMode.StepOut`). -/
def stepPost (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (Φ : val → IProp GF) : IProp GF :=
  -- (2026-10-14, stage R) the later credit of `raft.Step`'s precondition, for the branch's
  -- ghost step (`ghost_step_md`: the commit invariant's registry half opened around it)
  iprop(£ 1 ∗ ∀ (err : GoInterface) (s' : NState) (c' : CfgM) (md' : GMode),
    ("Hphys" ∷ ownRaftPhysCV c' c'.voters r id s' ∗
     "Hghost" ∷ ownStepGhost γ md' c' id s' ∗
     "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
     "%Hrefines" ∷ ⌜md.StepOut c id m s s' md'⌝ ∗
     "%Hcfg'" ∷ ⌜m.Type' ≠ MsgSnap → c' = c⌝ ∗
     "%Hframe" ∷ ⌜m.Type' ≠ MsgSnap → NetFrame s s'⌝ ∗
     "%Hterm" ∷ ⌜m.Type' ≠ MsgSnap → TermStep m s s'⌝ ∗
     "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
     "Herr" ∷ (⌜err = interface.nil⌝ ∨
               (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err))) -∗ Φ #err)

/-- What the dynamic mode's update needs of a step from `s` to `s'` (`DynHyp`), given the
invariant: from `raft.Step`'s premises (`GMode.Pre.dynHyp`). -/
def DynHypFor (md : GMode) (m : MessageM) (s s' : NState) : Prop :=
  ∀ (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) (g : RGh), md = .dyn dec c0 h0 g →
    RInv dec c0 (rOf s g) → DynHyp m s s' g

namespace StepProof

/-- The frame and the term step of a branch that keeps the term and the log's fields
`NetFrame` and `TermStep` are about (each `rfl` for a state built by record updates
that do not touch them). -/
theorem keep_frame {m : MessageM} {s s' : NState} (ht : s'.term = s.term)
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
theorem keep_frame_logst {m : MessageM} {s s' : NState} (ht : s'.term = s.term)
    (hl : s'.logst = s.logst) (hpv : s'.prevote = s.prevote := by rfl)
    (hg : s'.gh = s.gh := by rfl) :
    NetFrame s s' ∧ TermStep m s s' := by
  exact keep_frame ht (by rw [hl]) (by rw [hl]) (by rw [hl]) (by rw [hl]) (by rw [hl])
    (by rw [hl]) (by rw [hl]) hpv hg

/-- The same, for a branch that steps down to the message's term (`becomeFollower`) and
keeps the rest. -/
theorem stepdown_frame {m : MessageM} {s s' : NState} (hup : m.Type' ≠ MsgHup)
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
theorem stepdown_frame' {m : MessageM} {s s1 s' : NState} {l : w64}
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
theorem ghost_rdOk (γ : RaftNames) (id : w64) (s : NState) (Hr : s.role = .leader)
    {md : Bool} (V : GSet w64) :
    ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md -∗ ⌜RdOk V s.rd ∧ s.term ≠ W64 0⌝ := by
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
theorem ghost_hbResp_ctx (γ : RaftNames) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (ctx : List w8) (Hr : s.role = .leader) (Hto : m.To' = id)
    (Hteq : m.Term' = s.term) {md : Bool} :
    ⊢ ownRaftGhost (GF := GF) γ id (toPState s) md -∗ isMessage γ (absMsg .heartbeatResp m ents ctx) -∗
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

/-- The static mode's ghost update of a branch (a snapshot's, which the dynamic mode excludes):
`recv` is the incoming message, some number of times, and that message is `isMessage`. -/
theorem ghost_step_recv (γ : RaftNames) (c : CfgM) (id : w64)
    (ps ps' : PState) (a : Msg) (recv : List Msg)
    (HC : CfgStatic γ c) (Hrecv : ∀ m' ∈ recv, m' = a) (Hstep : StepC c id ps recv ps')
    (Hna : a.ty ≠ .readIndex) :
    ⊢ isMessage (GF := GF) γ a -∗ £ 1 -∗ ownRaftGhost γ id ps ={⊤}=∗ ownRaftGhost γ id ps' := by
  iintro #Hm Hlc Hg
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
  iapply ownRaftGhost_stepC γ c HC id ps recv ps' Hstep $$ Hall [Hz] Hlc Hg
  rw [Hcnt]; iexact Hz

/-- The one ghost update of a branch, in the mode `md`: `recv` is the incoming message, some
number of times, and that message is `isMessage`; its read credit when it is a read-index
request (`Hcr`). -/
theorem ghost_step_md (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM)
    (s s' : NState) (a : Msg) (recv : List Msg) (n : Nat)
    (Hrecv : ∀ m' ∈ recv, m' = a) (Hstep : StepCD c id m s recv s') (Hdh : DynHypFor md m s s')
    (Hn : rdCount recv ≤ n) :
    ⊢ isMessage (GF := GF) γ a -∗ rdCred γ n -∗ £ 1 -∗ ownRaftGhost γ id (toPState s) md.isDyn -∗
      ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗ ownStepGhost γ md' c id s' := by
  iintro #Hm Hcr Hlc Hg Hrest
  ihave Hall : ([∗list] m ∈ recv, isMessage (GF := GF) γ m) $$ []
  · iapply (BigSepL.bigSepL_intro (P := iprop(□ isMessage (GF := GF) γ a))
      (fun k x hx => by
        rw [Hrecv x (List.mem_of_getElem? hx)]
        exact intuitionistically_elim))
    iexact Hm
  ihave Hc := (rdCred_split γ (rdCount recv) (n - rdCount recv)).1 $$ [Hcr]
  · rw [show rdCount recv + (n - rdCount recv) = n by omega]; iexact Hcr
  icases Hc with ⟨Hc, -⟩
  imod ghost_stepCD γ md c id m s recv s' Hstep Hdh $$ Hall Hc Hlc Hg Hrest
    with ⟨%md', %Hout, Hg, Hrest⟩
  imodintro
  iexists md'
  isplitr
  · ipureintro; exact Hout
  unfold ownStepGhost
  iframe

/-- The same, for a branch that receives nothing. -/
theorem ghost_step_md0 (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM)
    (s s' : NState) (Hstep : StepCD c id m s [] s') (Hdh : DynHypFor md m s s') :
    ⊢ £ 1 -∗ ownRaftGhost (GF := GF) γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s ={⊤}=∗
      ∃ md', ⌜md.StepOut c id m s s' md'⌝ ∗ ownStepGhost γ md' c id s' := by
  iintro Hlc Hg Hrest
  imod rdCred_zero (GF := GF) γ with Hcr
  imod ghost_stepCD γ md c id m s [] s' Hstep Hdh $$ [] [Hcr] Hlc Hg Hrest
    with ⟨%md', %Hout, Hg, Hrest⟩
  · iapply (BigSepL.bigSepL_nil (Φ := fun _ m => isMessage (GF := GF) γ m)).2
    iempintro
  · rw [show rdCount ([] : List Msg) = 0 from rfl]; iexact Hcr
  imodintro
  iexists md'
  isplitr
  · ipureintro; exact Hout
  unfold ownStepGhost
  iframe

/-- A branch's postcondition, delivered: the ghost step, then `Φ`. -/
theorem finish_branch (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64)
    (s s' : NState) (m : MessageM) (a : Msg) (recv : List Msg) (err : GoInterface)
    (Φ : val → IProp GF)
    (Hdh : DynHypFor md m s s') (Hwf' : NStateWf s') (Hrecv : ∀ m' ∈ recv, m' = a)
    (Hstep : StepCD c id m s recv s')
    (Hfr : m.Type' ≠ MsgSnap → NetFrame s s') (Htm : m.Type' ≠ MsgSnap → TermStep m s s')
    (Hresp : RespStep m s s') (Hna : a.ty ≠ .readIndex := by simp [absMsg, absMsgFrom]) :
    ⊢ isMessage γ a -∗
      ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      ownRaftPhysCV c c.voters r id s' -∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err)) -∗
      stepPost γ md c r id s m Φ -∗
      |={⊤}=> Φ #err := by
  iintro #Hm Hghost Hrest Hphys Herr HΦ
  have Hcnt : rdCount recv = 0 := by
    unfold rdCount; rw [List.countP_eq_zero]
    intro x hx; rw [Hrecv x hx]; simp [Hna]
  imod rdCred_zero (GF := GF) γ with Hz
  unfold stepPost
  icases HΦ with ⟨Hlc, HΦ⟩
  imod ghost_step_md γ md c id m s s' a recv 0 Hrecv Hstep Hdh (by omega) $$ Hm Hz Hlc Hghost Hrest
    with ⟨%md', %Hout, Hghost⟩
  imodintro
  iapply HΦ $$ %err %s' %c %md'
  iframe Hphys Hghost Herr
  ipureintro
  exact ⟨Hwf', Hout, fun _ => rfl, Hfr, Htm, Hresp⟩

/-- The same, for a branch that consumed nothing. -/
theorem finish_branch0 (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64)
    (s s' : NState) (m : MessageM) (err : GoInterface) (Φ : val → IProp GF)
    (Hdh : DynHypFor md m s s') (Hwf' : NStateWf s')
    (Hstep : StepCD c id m s [] s')
    (Hfr : m.Type' ≠ MsgSnap → NetFrame s s') (Htm : m.Type' ≠ MsgSnap → TermStep m s s')
    (Hresp : RespStep m s s') :
    ⊢ ownRaftGhost γ id (toPState s) md.isDyn -∗ ghostRest γ md c id s -∗
      ownRaftPhysCV c c.voters r id s' -∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err)) -∗
      stepPost γ md c r id s m Φ -∗
      |={⊤}=> Φ #err := by
  iintro Hghost Hrest Hphys Herr HΦ
  unfold stepPost
  icases HΦ with ⟨Hlc, HΦ⟩
  imod ghost_step_md0 γ md c id m s s' Hstep Hdh $$ Hlc Hghost Hrest with ⟨%md', %Hout, Hghost⟩
  imodintro
  iapply HΦ $$ %err %s' %c %md'
  iframe Hphys Hghost Herr
  ipureintro
  exact ⟨Hwf', Hout, fun _ => rfl, Hfr, Htm, Hresp⟩

end StepProof

end base

end EtcdGrove
end Perennial
