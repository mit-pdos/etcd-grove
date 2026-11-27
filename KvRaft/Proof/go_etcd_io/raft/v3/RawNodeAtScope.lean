-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNodeAtScope.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (#33 S4, P-raft-3, `notes/antithesis-rawnode-design.md` §2.7). **The harness's scope at a
node's state, for the strengthened `RawNode` proofs**: the lifting lemmas' scope (`LiftScope`,
`InputEndLift.lean`) from `ownRawNodeAt`'s scope (`RnScopeBasic`) and the node's resources
(`liftScope_of`: the tally of a follower empty, `ownRaftGhost`'s; the progress map's halves, the
tracker's; the node one of the static configuration's voters, `CfgStatic`); the configuration of a
static node's end relations (`rnCfg`) by its voters (`TickEnd.of_voters`); and the scope's owned part
carried to the end state (`rnScopeAt_keepIf`).
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeAtLemmas
public import KvRaft.Proof.go_etcd_io.raft.v3.InputEndLift

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable {k : NodeK}
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `toPState`'s read-index requests are the node's (`rdNL` keeps them). -/
theorem toPState_rd_pend (s : NState) : (toPState s).rd.pend = s.rd.pend := by
  show (if s.role = .leader then s.rd else rdNL s.rd).pend = _
  split <;> rfl

/-- The harness's static configuration's voters (`rnCfg`). -/
theorem rnCfg_voters (γ : RaftNames) : (rnCfg γ).voters = γ.reCfg :=
  CfgM.voters_of_out rfl

/-- `TickEnd` reads the configuration's voters and ids only. -/
theorem TickEnd.of_voters {c c' : CfgM} {id : w64} {s s' : PState} (hv : c.voters = c'.voters)
    (hd : c.ids = c'.ids) (h : TickEnd k c id s s') : TickEnd k c' id s s' := by
  unfold TickEnd CampaignEnd PreCampaignEnd at h ⊢; rwa [← hv, ← hd]

/-- **`LiftScope` from the pieces**: `RnScopeBasic`'s flags, no pre-candidate with pre-vote off, a
follower's tally empty, the progress map's halves, and the node in the configuration. -/
theorem liftScope_of {c : CfgM} {id : w64} {rs : RNState} {s : NState} (H : RnScopeBasic rs s)
    (Hpre : s.role = .preCandidate → s.prevote = true) (Hfv : FollowerVotesOk (toPState s))
    (Hd1 : domSet s.prvals = domSet s.progress) (Hd2 : domSet s.progress = c.ids)
    (Hid : id ∈ c.voters) : LiftScope c id s := by
  obtain ⟨-, Hpv, Hcq, Hrd, -⟩ := H
  refine ⟨Hpv, Hcq, fun h => (by have := Hpre h; rw [Hpv] at this; cases this), Hfv, Hrd, Hd1, ?_, Hd2⟩
  rw [Hd1, Hd2]
  exact GMap.elem_of_union_l c.learners Hid

/-- (#33 S4, msgShape) `RnScopeBasic`'s read-only conjunct at the protocol reading: a non-leader's
read-only object reads as the fresh one (`rdNL`). -/
theorem roEmpty_iff (s : NState) :
    (s.role = .leader → s.rd.ro.pending = []) ↔ (toPState s).rd.ro.pending = [] := by
  unfold toPState
  by_cases hr : s.role = .leader
  · simp only [hr, ite_true, true_implies]
  · simp only [hr, ite_false, false_implies, true_iff]; rfl

/-- **The scope at the end state of an input** that keeps the log's state (`hl`), pre-vote and
check-quorum (`hpv`, `hcq`), the read-index requests (`hrd`), an empty read-only queue (`hro`), and
queues no `MsgSnap` (`ho`), and steps no transfer request (`hxs`, by default from the ghost state
kept: a step other than a transfer request's frames it, `NetFrame`). -/
theorem RnScopeBasic.keep {rs rs' : RNState} {s s' : NState} (H : RnScopeBasic rs s)
    (hm : rs'.mode = rs.mode) (hsl : rs'.slent = rs.slent)
    (hpv : s'.prevote = s.prevote) (hcq : s'.cq = s.cq) (hrd : s'.rd.pend = s.rd.pend)
    (hprev : s'.logst.prev = s.logst.prev) (hsn : s'.logst.snap = s.logst.snap)
    (ho : ∀ m ∈ s'.outbox, m ∈ s.outbox ∨ m.ty ≠ .snap)
    (hro : (toPState s).rd.ro.pending = [] → (toPState s').rd.ro.pending = [])
    (hcf : rs'.cfg = rs.cfg := by rfl)
    (hxs : s'.gh.xs = s.gh.xs := by
      first | rfl | (apply congrArg NGhost.xs; assumption) |
        (apply congrArg NGhost.xs; apply Eq.symm; assumption)) :
    RnScopeBasic rs' s' := by
  obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩ := H
  refine ⟨by rw [hm, hcf]; exact H1, hpv.trans H2, hcq.trans H3, hrd.trans H4, hsl.trans H5,
    hprev.trans H6, hsn.trans H7, fun m hm' => ?_, (roEmpty_iff s').2 (hro ((roEmpty_iff s).1 H9)),
    hxs.trans H10⟩
  rcases ho m hm' with h | h
  · exact H8 m h
  · exact h

/-- (#33 S4, msgShape) A tick keeps the read-only queue empty: a campaign is no leader, a leader's
heartbeats touch no read state. -/
theorem tickEnd_ro {c : CfgM} {id : w64} {s s' : PState} (hT : TickEnd k c id s s')
    (h : s.rd.ro.pending = []) : s'.rd.ro.pending = [] := by
  rcases hT with rfl | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, ms, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact h
  · rfl
  · exact h
  · exact h
  · rfl

/-- (antithesis parity) Answering read requests keeps the read-only object and the deferred
requests. -/
theorem preadRespondAll_ro_pend (id : w64) (s : PState) (qs : List ReadReq) :
    (preadRespondAll id s qs).rd.ro = s.rd.ro ∧ (preadRespondAll id s qs).rd.pend = s.rd.pend := by
  unfold preadRespondAll
  induction qs generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons q qs ih =>
    rw [List.foldl_cons]
    have h1 : (preadRespond id s q).rd.ro = s.rd.ro ∧ (preadRespond id s q).rd.pend = s.rd.pend := by
      unfold preadRespond
      split
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    obtain ⟨a, b⟩ := ih (preadRespond id s q)
    exact ⟨a.trans h1.1, b.trans h1.2⟩

/-- (antithesis parity) A read acknowledgement keeps the deferred requests, and an empty read-only
queue empty. -/
theorem ReadAckEnd.rd {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (h : ReadAckEnd c id s m s') :
    s'.rd.pend = s.rd.pend ∧ (s.rd.ro.pending = [] → s'.rd.ro.pending = []) := by
  have hra : (readonlyRecvAck s.rd.ro m.src m.ctx).pending = s.rd.ro.pending := by
    unfold readonlyRecvAck; split <;> rfl
  rcases h with ⟨-, rfl⟩ | ⟨N, -, rfl⟩
  · exact ⟨rfl, fun hp => hra.trans hp⟩
  · obtain ⟨h1, h2⟩ := preadRespondAll_ro_pend id
      { s with rd := { s.rd with ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1 } }
      (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).2
    refine ⟨h2, fun hp => ?_⟩
    rw [h1]
    show (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1.pending = []
    unfold readonlyAdvance
    split
    · exact hra.trans hp
    · simp only [hra, hp, List.drop_nil]

/-- (antithesis parity) The commit's release, with no request deferred: the read-only object kept,
none deferred after. -/
theorem ReleaseEnd.rd {c : CfgM} {id : w64} {s s' : PState} (h : ReleaseEnd c id s s')
    (hpd : s.rd.pend = []) : s'.rd.pend = [] ∧ s'.rd.ro = s.rd.ro := by
  rcases h with ⟨-, hb, -, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨rfl, ?_⟩
    show readonlyRelease s.rd.ro id s.commit s.rd.pend = s.rd.ro
    rw [hpd]; rfl
  · exact ⟨(preadRespondAll_ro_pend id _ _).2, (preadRespondAll_ro_pend id _ _).1⟩

/-- (#33 S4, msgShape) A message of the harness's types keeps the read-only queue empty (no read
index; a new leader's `reset` installs a fresh one, `rdNL`); (antithesis parity) with no read
request deferred (a commit's release). -/
theorem handleEnd_ro {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : HandleEnd k c id s m s') (hpd : s.rd.pend = []) (hp : s.rd.ro.pending = []) :
    s'.rd.ro.pending = [] := by
  unfold HandleEnd at h
  rcases hty with e | e | e | e | e | e <;> rw [e] at h <;> simp only at h
  · split at h
    · subst h; exact hp
    · unfold AppEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩ <;> exact hp
  · split at h
    · unfold AppRespEnd SendsEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, _, -, rfl⟩ | ⟨-, _, _, -, -, _, -, rfl⟩ |
        ⟨-, _, _, s2, -, -, hrel, _, -, rfl⟩
      · exact hp
      · exact hp
      · exact hp
      · show s2.rd.ro.pending = []
        rw [(hrel.rd hpd).2]; exact hp
    · subst h; exact hp
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact hp
  · split at h
    · unfold WinEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact hp
      · rfl
      · rfl
    · subst h; exact hp
  · split at h <;> (subst h; first | exact hp | rfl)
  · split at h
    · obtain ⟨s2, ⟨_, -, rfl⟩, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact hp
      · exact ha.rd.2 hp
    · subst h; exact hp

/-- (antithesis parity) The handled step of a message of the harness's types keeps the read-index
requests, with none deferred (a commit's release). -/
theorem handleEnd_rd_pend {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : HandleEnd k c id s m s') (hpd : s.rd.pend = []) : s'.rd.pend = s.rd.pend := by
  unfold HandleEnd at h
  rcases hty with e | e | e | e | e | e <;> rw [e] at h <;> simp only at h
  · split at h
    · subst h; rfl
    · unfold AppEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩ <;> rfl
  · split at h
    · unfold AppRespEnd SendsEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, _, -, rfl⟩ | ⟨-, _, _, -, -, _, -, rfl⟩ |
        ⟨-, _, _, s2, -, -, hrel, _, -, rfl⟩
      · rfl
      · rfl
      · rfl
      · show s2.rd.pend = s.rd.pend
        rw [(hrel.rd hpd).1, hpd]
    · subst h; rfl
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  · split at h
    · unfold WinEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    · subst h; rfl
  · split at h <;> (subst h; rfl)
  · split at h
    · obtain ⟨s2, ⟨_, -, rfl⟩, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · rfl
      · exact ha.rd.1
    · subst h; rfl

/-- `Step`'s preamble keeps the deferred read requests. -/
theorem PreEnd.rd_pend {s : PState} {m : Msg} {s1 : PState} (hp : PreEnd k s m s1) :
    s1.rd.pend = s.rd.pend := by
  rcases hp with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl

/-- A stale message's end keeps the read state. -/
theorem StaleEnd.rd {id : w64} {s : PState} {m : Msg} {s' : PState} (h : StaleEnd k id s m s') :
    s'.rd = s.rd := by
  rcases h with rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

theorem recvEnd_ro {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : RecvEnd k c id s m s') (hpd : s.rd.pend = []) (hp : s.rd.ro.pending = []) :
    s'.rd.ro.pending = [] := by
  rcases h with ⟨-, h⟩ | ⟨-, -, hs⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, h⟩
  · exact handleEnd_ro hty h hpd hp
  · rw [hs.rd]; exact hp
  · exact hp
  · refine handleEnd_ro hty h (by rw [hpre.rd_pend]; exact hpd) ?_
    rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · rfl
    · exact hp
    · exact hp

/-- **The read-index requests kept** by a received message of the harness's types, with none
deferred. -/
theorem recvEnd_rd_pend {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : RecvEnd k c id s m s') (hpd : s.rd.pend = []) : s'.rd.pend = s.rd.pend := by
  rcases h with ⟨-, h⟩ | ⟨-, -, hs⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, h⟩
  · exact handleEnd_rd_pend hty h hpd
  · rw [hs.rd]
  · rfl
  · rw [handleEnd_rd_pend hty h (by rw [hpre.rd_pend]; exact hpd), hpre.rd_pend]

/-- (2026-11-24) **The harness's configuration at a node in the scope**: the incoming voters the
names', no outgoing half (`CfgStatic`'s first two conjuncts, in either mode). -/
def CfgScope (γ : RaftNames) (c : CfgM) : Prop :=
  c.incoming = γ.reCfg ∧ c.outgoing = ∅ ∧ True

theorem CfgScope.voters {γ : RaftNames} {c : CfgM} (HC : CfgScope γ c) : c.voters = γ.reCfg := by
  rw [CfgM.voters_of_out HC.2.1, HC.1]

/-- (#33 S4, destinations) With no learners (`RnCfgInBasic.learners`), the configuration's ids are
the static configuration's (`rnCfg`). -/
theorem CfgScope.ids {γ : RaftNames} {c : CfgM} (HC : CfgScope γ c) (hl : c.learners = ∅) :
    c.ids = (rnCfg γ).ids := by
  unfold CfgM.ids; rw [HC.voters, rnCfg_voters, hl]; rfl

/-- `CfgScope` from the mode's configuration facts (`ownStepGhost_cfgScope`) and the scope's. -/
theorem cfgScope_of {γ : RaftNames} {id : w64} {rs : RNState} {s : NState} {c : CfgM}
    (Hs : RnScopeBasic rs s) (Hc : RnCfgInBasic γ id rs)
    (Hm : (rs.mode.isDyn = false → CfgStatic γ c) ∧ (rs.mode.isDyn = true → rs.cfg.cfg = c)) :
    CfgScope γ c ∧ id ∈ γ.reCfg := by
  refine ⟨?_, Hc.1⟩
  cases hd : rs.mode.isDyn
  · have H := Hm.1 hd; exact ⟨H.1, H.2.1, trivial⟩
  · rw [← Hm.2 hd]; exact ⟨Hc.2.1 hd, Hs.1 hd, trivial⟩

/-- (#33 S4, destinations) In the scope the configuration has no learners (`RnCfgInBasic`: the dynamic
mode's configuration has none). -/
theorem RnCfgInBasic.learners {γ : RaftNames} {id : w64} {rs : RNState} {c : CfgM} (Hc : RnCfgInBasic γ id rs)
    (Hm : (rs.mode.isDyn = false → CfgStatic γ c) ∧ (rs.mode.isDyn = true → rs.cfg.cfg = c)) :
    c.learners = ∅ := by
  rw [← Hm.2 Hc.2.2.2.1]; exact Hc.2.2.2.2

/-- A tick's end relation keeps the read-index requests and queues no `MsgSnap`: a campaign's votes,
a leader's heartbeats. -/
theorem tickEnd_rd_out {c : CfgM} {id : w64} {s s' : NState}
    (hT : TickEnd k c id (toPState s) (toPState s')) :
    s'.rd.pend = s.rd.pend ∧ ∀ m ∈ s'.outbox, m ∈ s.outbox ∨ m.ty ≠ .snap := by
  have ho : s'.outbox = (toPState s').outbox := rfl
  have ho0 : s.outbox = (toPState s).outbox := rfl
  rw [← toPState_rd_pend s', ← toPState_rd_pend s, ho, ho0]
  rcases hT with h | ⟨-, -, -, peers, -, h⟩ | ⟨-, -, -, peers, -, h⟩ | ⟨-, ms, hms, h⟩ | ⟨-, -, h⟩
  · rw [h]; exact ⟨rfl, fun m hm => .inl hm⟩
  · rw [h]
    refine ⟨rfl, fun m hm => ?_⟩
    rw [psendMsgs_outbox, List.mem_append] at hm
    rcases hm with hm | hm
    · exact .inl hm
    · right
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · rw [List.mem_singleton] at hm; subst hm; simp [Msg.plain]
      · obtain ⟨d, -, rfl⟩ := List.mem_map.1 hm; simp [pvoteReq]
  · rw [h]
    refine ⟨rfl, fun m hm => ?_⟩
    rw [psendMsgs_outbox, List.mem_append] at hm
    rcases hm with hm | hm
    · exact .inl hm
    · right
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · rw [List.mem_singleton] at hm; subst hm; simp [Msg.plain]
      · obtain ⟨d, -, rfl⟩ := List.mem_map.1 hm; simp [pvoteReq]
  · rw [h]
    refine ⟨rfl, fun m hm => ?_⟩
    rw [psendMsgs_outbox, List.mem_append] at hm
    rcases hm with hm | hm
    · exact .inl hm
    · right; rw [(hms m hm).1.1]; decide
  · rw [h]; exact ⟨rfl, fun m hm => .inl hm⟩

end pure

section ghost
variable {k : NodeK}
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A follower's tally is empty (`ownRaftGhost_follower_votes`, through `ownStepGhost`). -/
theorem ownStepGhost_followerVotes (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜FollowerVotesOk (toPState s)⌝ ∗ ownStepGhost γ md c id s := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  ihave %Hfv := ownRaftGhost_follower_votes γ id (toPState s) $$ Hg
  isplitr
  · ipureintro; exact Hfv
  iunfold ownStepGhost
  iframe Hg Hr

/-- Statically, the configuration is the ghost state's (`ghostRestM`'s `CfgStatic`). -/
theorem ownStepGhost_cfgStatic (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜md = .static → CfgStatic γ c⌝ ∗ ownStepGhost γ md c id s := by
  cases md with
  | static =>
    iintro H
    iunfold ownStepGhost at H
    icases H with ⟨Hg, Hr⟩
    iunfold ghostRest at Hr
    icases Hr with ⟨Hn, Hm, Hr⟩
    ihave %HC : ⌜CfgStatic γ c ∧ TrackedOk γ c id⌝ $$ [Hm]
    · simp only [ghostRestM]; iexact Hm
    isplitr
    · ipureintro; intro _; exact HC.1
    iunfold ownStepGhost
    iframe Hg
    iunfold ghostRest
    iframe Hn Hr
    simp only [ghostRestM]
    ipureintro; exact HC
  | dyn dec c0 h0 g =>
    iintro H
    iframe H
    ipureintro; intro h; cases h

/-- (2026-11-24) **The configuration, by mode**: statically `CfgStatic`; dynamically the ghost
state's (`ghostRestM`'s `g.cfg.cfg = c`, `g.cfg` the node's `rs.cfg`). -/
theorem ownStepGhost_cfgScope (γ : RaftNames) (rs : RNState) (fp : List EntryM) (ds : DecMap)
    (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id s ⊢
      ⌜(rs.mode.isDyn = false → CfgStatic γ c) ∧ (rs.mode.isDyn = true → rs.cfg.cfg = c)⌝ ∗
      ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id s := by
  cases hm : rs.mode with
  | static =>
    iintro H
    icases ownStepGhost_cfgStatic γ _ c id s $$ H with ⟨%Hcfs, H⟩
    iframe H
    ipureintro
    exact ⟨fun _ => Hcfs rfl, fun h => by cases h⟩
  | dyn dec c0 h0 h1 =>
    iintro H
    iunfold ownStepGhost at H
    icases H with ⟨Hg, Hr⟩
    iunfold ghostRest at Hr
    icases Hr with ⟨Hn, Hm, Hr⟩
    simp only [RNMode.toG, ghostRestM]
    icases Hm with ⟨%HC, Hm⟩
    isplitr
    · ipureintro; exact ⟨fun h => (by cases h), fun _ => HC.2.1⟩
    iunfold ownStepGhost
    iframe Hg
    iunfold ghostRest
    iframe Hn Hr
    simp only [ghostRestM]
    iframe Hm
    ipureintro; exact HC

/-- The progress map's halves agree, and track the configuration's ids. -/
theorem ownRaftPhysC_trkDoms (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜domSet s.prvals = domSet s.progress ∧ domSet s.progress = c.ids⌝ ∗
      ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_tracker c r id s $$ H with ⟨%tv, Hf, Htrk, Hback⟩
  icases ownTrackerC_pure c tv _ $$ Htrk with ⟨%Hp, Htrk⟩
  icases ownTrackerC_prvals_dom c tv _ $$ Htrk with ⟨%Hd, Htrk⟩
  isplitr
  · ipureintro; exact ⟨Hd, Hp.2.1⟩
  iapply Hback $$ %tv %s.votes Hf Htrk

/-- (antithesis parity B1) **The ghost prefix in the dynamic mode at the boundary `base0`**: empty
(the dynamic model's invariant `RInv`, `full`: `FullOk base0 fp`). -/
theorem ownStepGhost_fp_nil (γ : RaftNames) (rs : RNState) (fp : List EntryM) (ds : DecMap)
    (c : CfgM) (id : w64) (s : NState) (hd : rs.mode.isDyn = true) (hb : s.logst.prev = base0) :
    ownStepGhost (GF := GF) γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id s ⊢
      ⌜fp = []⌝ ∗ ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) c id s := by
  cases hm : rs.mode with
  | static => rw [hm] at hd; cases hd
  | dyn dec c0 h0 h1 =>
    iintro H
    iunfold ownStepGhost at H
    icases H with ⟨Hg, Hr⟩
    iunfold ghostRest at Hr
    icases Hr with ⟨Hn, Hm, Hr⟩
    simp only [RNMode.toG, ghostRestM]
    icases Hm with ⟨%HC, Hm⟩
    isplitr
    · ipureintro
      have Hf := HC.2.2.full
      have h1 := Hf.1
      simp only [rOf] at h1
      rw [show (toPState s).base = s.logst.prev from rfl, hb, base0_index] at h1
      exact List.eq_nil_of_length_eq_zero (by omega)
    iunfold ownStepGhost
    iframe Hg
    iunfold ghostRest
    iframe Hn Hr
    simp only [ghostRestM]
    iframe Hm
    ipureintro; exact HC

/-- (antithesis parity B1) **In the basic scope, the `RState`'s ghost prefix is empty** (and its log's
boundary `base0`): `ownStepGhost_fp_nil` at the scope's boundary and dynamic mode. -/
theorem ownRawNodeAt_fp_nil (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState)
    (qs : List Msg) (ip : Nat) (sc : Bool) :
    ownRawNodeAt (GF := GF) γ rn id rs r qs ip (basicScope sc) ⊢
      ⌜sc = true → r.fp = [] ∧ r.p.base = base0⌝ ∗ ownRawNodeAt γ rn id rs r qs ip (basicScope sc) := by
  cases sc with
  | false => iintro H; iframe H; ipureintro; intro h; cases h
  | true =>
    iintro H
    iNamed H
    icases rnScopeAt_scope true rs s $$ Hsc with ⟨%Hscope, Hsc⟩
    icases rnScopeAt_cfgIn true rs s $$ Hsc with ⟨%Hcin, Hsc⟩
    icases ownStepGhost_fp_nil γ rs fp ds cf id s (Hcin rfl).2.2.2.1 (Hscope rfl).2.2.2.2.2.1
      $$ Hghost with ⟨%Hfp, Hghost⟩
    isplitr
    · ipureintro; intro _; subst Hps Hfp
      exact ⟨rfl, (Hscope rfl).2.2.2.2.2.1⟩
    unfold ownRawNodeAt
    iexists s, cf, fp, ds, rnv, sv, hprev, steps
    iframe Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc Hsloc Hhist
      Hledger Hdur Hrntr Hsc
    ipureintro
    exact ⟨Hwf, Hin, Hasync, Hdlen, Hunp, Hsnap, Hstok, Htrm, Hstor, Hpvoff, Hrs_out,
      Hrs_unst, Hrs_clb, Hrnfl, Hloan, Hsdt, Hrole, Hphs, Hgtr, Hglq, Hps, Hip⟩

/-- (antithesis parity B1) The node constant's tie across a step in the basic scope: pre-vote and
check-quorum off at both ends, `stepDownOnRemoval` kept (`hsdr`), the constant kept (`hk`). -/
theorem KTie.keep_basic {rs rs' : RNState} {s s' : NState} (H : KTie rs s) (Hs : RnScopeBasic rs s)
    (Hs' : RnScopeBasic rs' s') (hsdr : s'.sdr = s.sdr) (hk : rs'.k = rs.k) : KTie rs' s' := by
  unfold KTie at *
  rw [hk, ← H, hsdr, Hs.2.1, Hs.2.2.1, Hs'.2.1, Hs'.2.2.1]

/-- **The basic scope's owned part at the end state**: the scope's facts carried (`H`), the storage
the same, and (antithesis parity B1) `stepDownOnRemoval` and the node constant kept (`hsdr`, `hk`). -/
theorem rnScopeAt_keepIf {γ : RaftNames} {id : w64} (sc : Bool) (rs rs' : RNState) (s s' : NState)
    (H : sc = true → RnScopeBasic rs s → RnScopeBasic rs' s') (hst : s'.logst.storage = s.logst.storage)
    (hsdr : sc = true → s'.sdr = s.sdr)
    (hcf : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg := by exact ⟨rfl, rfl⟩)
    (hk : rs'.k = rs.k := by rfl) :
    rnScopeAt (GF := GF) γ id (basicScope sc) rs s ⊢ rnScopeAt γ id (basicScope sc) rs' s' := by
  cases sc with
  | false => unfold basicScope; iintro -; iapply rnScopeAt_none
  | true =>
    unfold rnScopeAt basicScope
    iintro ⟨%Hs, #Hc⟩
    rw [hst]
    isplitr
    · ipureintro
      have H0 := (RnScope_empty rs s).1 Hs.1
      have H1 := H rfl H0
      exact ⟨(RnScope_empty rs' s').2 H1, RnCfgIn.keep hcf Hs.2.1,
        Hs.2.2.1.keep_basic H0 H1 (hsdr rfl) hk, fun h => absurd h (by decide)⟩
    · imodintro; iexact Hc

end ghost

end EtcdGrove
end Perennial
