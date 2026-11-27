/-
Lean-first (no Rocq counterpart).

# A `Ready`'s messages' shape and the logs' normality (#33 S4, drain)

`msgShape_core`: what `msgShape.stmt` (`MsgShapeStmt.lean`) says, but the two context clauses:
the log at the `Ready` is normal and every message to another node is from the node, of a type
the network carries or a proposal, its entries normal (`MShape`); a heartbeat response's context
is the context of the heartbeat its drain handles (the cause). Per input, as `Outbox.lean`'s
`outOk_reach`: a log grows only by a proposal's batch (`PropRepl` of normal entries: normal), a new
leader's empty entry (normal) or a received append's entries (the cause's, normal by premise); a
message carries no entries, the log's (an append, `AppOk`), or the cause's (a forwarded proposal).

`msgShape_of`: `msgShape.stmt` from `TickHbCtx`, a tick's heartbeats carry no context, which
`TickEnd` (`Protocol/InputEnd.lean`) says in its heartbeat arm (`x.ctx = []`, lifted from
`stepLeader`'s exact context, `hbCtx`, `[]` with no read request pending, the RawNode scope's):
`tickHbCtx`, and `msgShape := msgShape_of tickHbCtx`.

`dst_reach` (#33 S4, destinations): every message of the state a `Ready` is taken at to another
node is to one of the three (`DstIn`): a response to the handled message's sender (a node,
`NetOk`), a leader's appends and heartbeats to the configuration's peers (`AppSendOk`'s and
`TickEnd`'s `c.ids`, `cfgM3`'s the three), a campaign's requests to the voters, a forwarded proposal
to the leader hint (`LeadIn`, a node or none). `msgShape_of` concludes `ReadyMsgsToVoters` from it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShapeStmt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Outbox

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

section shape
variable [GooseExts]
variable {cf : CfgM} {N : Nat} {kk : NodeK} {md : RnMode}

/-! ## Normal logs -/

theorem entsNormal_append {a b : List EntryM} (ha : EntsNormal a) (hb : EntsNormal b) :
    EntsNormal (a ++ b) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact hb e he

theorem entsNormal_nil : EntsNormal ([] : List EntryM) := fun e he => by cases he

/-- `maybeAppend`'s log: the old log's entries or the batch's. -/
theorem entsNormal_maybeAppend {b prev : entryID} {es ents es' : List EntryM} {li : w64}
    (h : plogMaybeAppend b es prev ents = some (li, es')) (hes : EntsNormal es)
    (hents : EntsNormal ents) : EntsNormal es' := by
  unfold plogMaybeAppend at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    split
    · exact hes
    · unfold plogTruncateAppend
      split
      · exact hes
      · rename_i e0 rest heq
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hes e (List.mem_of_mem_take he)
        · exact hents e (List.mem_of_mem_drop he)
  · cases h

/-- The conf-change loop's batch of normal entries is normal (a refused conf change becomes the
empty normal entry). -/
theorem entsNormal_propRepl {es es' : List EntryM} (h : PropRepl es es') (hes : EntsNormal es) :
    EntsNormal es' := by
  induction h with
  | nil => exact entsNormal_nil
  | cons hab _ ih =>
    rename_i a b l1 l2
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rcases hab with rfl | ⟨-, rfl⟩
      · exact hes _ (List.mem_cons_self ..)
      · rfl
    · exact ih (fun x hx => hes x (List.mem_cons_of_mem _ hx)) e he

/-- Stamping keeps the types. -/
theorem entsNormal_stamp {es : List EntryM} (t li : w64) (hes : EntsNormal es) :
    EntsNormal (es.mapIdx (stamp t li)) := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp he
  show es[i].Type' = W32 0
  exact hes _ (List.getElem_mem hi)

/-- A new leader's log: the empty entry appended. -/
theorem entsNormal_win {id : w64} {s : PState} {mt : GMap w64 w64} (hl : EntsNormal s.log) :
    EntsNormal (pwinState id s mt).log := by
  unfold pwinState pappend
  exact entsNormal_append hl (fun e he => by rw [List.mem_singleton.mp he]; rfl)

/-- The type switch keeps the log normal, the handled message's entries normal when it appends
them (an append, a proposal); the read arms keep the log (`PKeep`). -/
theorem entsNormal_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hsc : RdTy m.ty)
    (hent : m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries) (hl : EntsNormal s.log)
    (h : HandleEnd kk c id s m s') : EntsNormal s'.log := by
  unfold HandleEnd at h
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at h; simp only at h; rw [(readIdxEnd_keep h).log]; exact hl
  · rw [hty] at h; simp only at h
    split at h
    · rcases h with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hl
    · subst h; exact hl
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact hl
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact hl
      · obtain ⟨mt, ms, -, -, rfl⟩ := hw
        exact entsNormal_win (s := { s with votes := _ }) hl
      · exact hl
    · subst h; exact hl
  · split at h
    · subst h; exact hl
    · rcases h with ⟨-, rfl⟩ | ⟨-, lastnewi, es', hma, rfl⟩ | ⟨-, -, -, -, -, -, rfl⟩
      · exact hl
      · exact entsNormal_maybeAppend hma hl (hent (.inl hty))
      · exact hl
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩ | ⟨-, x, n, s2, -, -, hrel, hs⟩
      · exact hl
      · obtain ⟨ms, -, rfl⟩ := hs; exact hl
      · obtain ⟨ms, -, rfl⟩ := hs; exact hl
      · obtain ⟨ms, -, rfl⟩ := hs
        show EntsNormal s2.log
        rw [(releaseEnd_keep hrel).log]; exact hl
    · subst h; exact hl
  · split at h
    · subst h; exact hl
    · subst h; exact hl
  · split at h
    · obtain ⟨s2, ⟨ms, -, rfl⟩, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact hl
      · rw [(readAckEnd_keep ha).log]; exact hl
    · subst h; exact hl
  · unfold ProposeEnd at h
    split at h
    · rcases h with rfl | ⟨es, ms, hrep, -, rfl⟩
      · exact hl
      · exact entsNormal_append hl
          (entsNormal_stamp _ _ (entsNormal_propRepl hrep (hent (.inr hty))))
    · split at h
      · subst h; exact hl
      · subst h; exact hl

theorem entsNormal_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hsc : RdTy m.ty)
    (hent : m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries) (hl : EntsNormal s.log)
    (h : RecvEnd kk c id s m s') : EntsNormal s'.log := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact entsNormal_handle hsc hent hl hh
  all_goals try exact hl
  obtain ⟨-, -, hl1, -, -⟩ := preEnd_facts (not_preTy hsc) hpre
  exact entsNormal_handle hsc hent (hl1 ▸ hl) hh

theorem entsNormal_tick {c : CfgM} {id : w64} {s s' : PState} (hl : EntsNormal s.log)
    (h : TickEnd kk c id s s') : EntsNormal s'.log := by
  rw [(tickEnd_keep h).1]; exact hl

theorem entsNormal_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (h : AdvanceEnd kk c id s qs s') (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp)
    (hl : EntsNormal s.log) : EntsNormal s'.log := by
  induction h with
  | nil => exact hl
  | cons s s1 s' q qs hr _ ih =>
    have hty := hq q (List.mem_cons_self ..)
    refine ih (fun x hx => hq x (List.mem_cons_of_mem _ hx)) (entsNormal_recv ?_ ?_ hl hr)
    · rcases hty with h' | h' <;> simp [RdTy, S4Ty, h']
    · rintro (h' | h') <;> rcases hty with h'' | h'' <;> rw [h''] at h' <;> cases h'

/-! ## No read request without reads -/

/-- No read request deferred, and a leader has none pending (`NodeFacts.roPend`'s body at a
protocol state). -/
def RoOk (s : PState) : Prop := s.rd.pend = [] ∧ (s.role = .leader → s.rd.ro.pending = [])

theorem roOk_win {id : w64} {s : PState} {mt : GMap w64 w64} (hp : s.rd.pend = []) :
    RoOk (pwinState id s mt) :=
  ⟨hp, fun _ => rfl⟩

theorem roOk_winEnd {c : CfgM} {id : w64} {X s' : PState} (h : WinEnd c id X s')
    (hp : X.rd.pend = []) : RoOk s' := by
  obtain ⟨mt, ms, -, -, rfl⟩ := h; exact ⟨hp, fun _ => rfl⟩

theorem roOk_sends {c : CfgM} {id : w64} {X s' : PState} (h : SendsEnd c id X s') (hX : RoOk X) :
    RoOk s' := by
  obtain ⟨ms, -, rfl⟩ := h; exact hX

theorem roOk_propose {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ProposeEnd c id s m s')
    (hs : RoOk s) : RoOk s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, -, rfl⟩
    · exact hs
    · exact hs
  · split at h
    · subst h; exact hs
    · subst h; exact hs

theorem roOk_appEnd {id : w64} {X s' : PState} {m : Msg} (h : AppEnd id X m s')
    (hX : X.role = .follower) (hp : X.rd.pend = []) : RoOk s' := by
  rcases h with ⟨-, rfl⟩ | ⟨-, lastnewi, es', -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩ <;>
    exact ⟨hp, fun h => by simp [psendMsgs, hX] at h⟩

/-- The release of no deferred request queues none. -/
theorem roOk_release {c : CfgM} {id : w64} {X s2 : PState} (h : ReleaseEnd c id X s2) (hX : RoOk X) :
    RoOk s2 := by
  rcases h with ⟨-, hb, -, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨rfl, fun hr => ?_⟩
    change (readonlyRelease X.rd.ro id X.commit X.rd.pend).pending = []
    rw [readonlyRelease_pending, hX.1, hX.2 hr]; simp
  · obtain ⟨-, hk, -⟩ := preadRespondAll_out id { X with rd := { X.rd with pend := [] } }
      (X.rd.pend.map (fun p => (⟨X.commit, p.1.From', p.2⟩ : ReadReq)))
    have hrd := preadRespondAll_rd id { X with rd := { X.rd with pend := [] } }
      (X.rd.pend.map (fun p => (⟨X.commit, p.1.From', p.2⟩ : ReadReq)))
    exact ⟨hrd.1, fun hr => by rw [hrd.2]; exact hX.2 (hk.role.symm.trans hr)⟩

/-- A read acknowledgement at a leader with no request pending answers none. -/
theorem roOk_readAck {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadAckEnd c id s m s')
    (hs : RoOk s) (hr : s.role = .leader) : RoOk s' := by
  have hp := hs.2 hr
  rcases h with ⟨-, rfl⟩ | ⟨N', -, rfl⟩
  · refine ⟨hs.1, fun _ => ?_⟩
    change (readonlyRecvAck s.rd.ro m.src m.ctx).pending = []
    rw [readonlyRecvAck_pending]; exact hp
  · have hrd := preadRespondAll_rd id
      { s with rd := { s.rd with ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N').1 } }
      (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N').2
    refine ⟨hrd.1.trans hs.1, fun _ => ?_⟩
    rw [hrd.2]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hq
    have := readonlyAdvance_pending (readonlyRecvAck s.rd.ro m.src m.ctx) N' q hq
    rw [readonlyRecvAck_pending, hp] at this; cases this

/-- The type switch keeps `RoOk` but for a read request: every arm keeps the read-only queue and
the role, makes the node a follower, or makes it leader (`pbecomeLeader` resets the queue); a
commit's release and a read acknowledgement find no request. -/
theorem roOk_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hs : RoOk s)
    (hsc : RdTy m.ty) (hnr : m.ty ≠ .readIndex) (h : HandleEnd kk c id s m s') : RoOk s' := by
  unfold HandleEnd at h
  rcases hsc with hs4 | hty | hty
  rotate_left
  · exact absurd hty hnr
  · rw [hty] at h; simp only at h
    split at h
    · rcases h with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hs
    · subst h; exact hs
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact hs
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact hs
      · exact roOk_winEnd hw hs.1
      · exact ⟨hs.1, fun h => by simp [pbecomeFollower] at h⟩
    · subst h; exact hs
  · split at h
    · subst h; exact hs
    · exact roOk_appEnd h rfl hs.1
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, -, hs'⟩ | ⟨-, x, n, -, -, hs'⟩ | ⟨-, x, n, s2, -, -, hrel, hs'⟩
      · exact hs
      · exact roOk_sends hs' hs
      · exact roOk_sends hs' hs
      · exact roOk_sends hs' (roOk_release (X := { s with matched := _, commit := n }) hrel hs)
    · subst h; exact hs
  · split at h
    · subst h; exact hs
    · subst h; exact ⟨hs.1, fun h => by simp [psendMsgs, padoptLeader] at h⟩
  · split at h
    · rename_i hr
      obtain ⟨s2, hs', ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact roOk_sends hs' hs
      · have hr2 : s2.role = .leader := by obtain ⟨ms, -, rfl⟩ := hs'; exact hr
        exact roOk_readAck ha (roOk_sends hs' hs) hr2
    · subst h; exact hs
  · exact roOk_propose h hs

theorem roOk_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hs : RoOk s)
    (hsc : RdTy m.ty) (hnr : m.ty ≠ .readIndex) (h : RecvEnd kk c id s m s') : RoOk s' := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact roOk_handle hs hsc hnr hh
  all_goals try exact hs
  refine roOk_handle ?_ hsc hnr hh
  rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
  · exact ⟨hs.1, fun h => by simp [pbecomeFollower] at h⟩
  · exact hs
  · exact hs

theorem roOk_tick {c : CfgM} {id : w64} {s s' : PState} (hs : RoOk s) (h : TickEnd kk c id s s') :
    RoOk s' := by
  rcases h with rfl | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, ms, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact hs
  · exact ⟨hs.1, fun h => by simp [psendMsgs, pbecomeCandidate] at h⟩
  · exact ⟨hs.1, fun h => by simp [psendMsgs] at h⟩
  · exact hs
  · exact ⟨hs.1, fun h => by simp [pbecomeFollower] at h⟩

theorem roOk_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg} (hs : RoOk s)
    (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp) (h : AdvanceEnd kk c id s qs s') :
    RoOk s' := by
  induction h with
  | nil => exact hs
  | cons s s1 s' q qs hr _ ih =>
    refine ih ?_ (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    rcases hq q (List.mem_cons_self ..) with h | h
    · exact roOk_recv hs (by simp [RdTy, S4Ty, h]) (by rw [h]; decide) hr
    · exact roOk_recv hs (by simp [RdTy, S4Ty, h]) (by rw [h]; decide) hr

/-- A received pre-vote request or response keeps `RoOk`: the answers keep the state, a
step-down or a campaign leaves no leader. -/
theorem roOk_recvP {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hs : RoOk s)
    (hty : m.ty = .preVote ∨ m.ty = .preVoteResp) (h : RecvEnd kk c id s m s') : RoOk s' := by
  rcases recvEnd_pre hty h with rfl | ⟨-, -, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, -, rfl⟩ |
      ⟨-, -, -, -, hcs⟩
  · exact hs
  · exact hs
  · exact hs
  · exact hs
  · exact ⟨hs.1, fun h => by simp [pbecomeFollower] at h⟩
  · obtain ⟨peers, -, rfl⟩ := hcs
    exact ⟨hs.1, fun h => by simp [psendMsgs, pbecomeCandidate] at h⟩

/-- **`RoOk` along `ReachP`** with no read request received (`hnrm`) or taken (`hnr`: a read
request's drain reached the view's own state). -/
theorem roOk_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView} {ps₁ : PState}
    (hs : RoOk v.ps) (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → q.ty = .appResp ∨ q.ty = .voteResp)
    (hnrm : ∀ m ∈ net, m.ty ≠ .readIndex) (hnr : v.Idle → v.byE = go!"read" → ps₁ = v.ps)
    (hr : ReachP kk c id net xnet v ps₁) : RoOk ps₁ := by
  cases hr with
  | stay _ => exact hs
  | recv m _ _ _ _ hmn _ _ hty h => exact roOk_recv hs hty (hnrm m hmn) h
  | recvP m _ _ _ _ _ _ _ hpt _ h => exact roOk_recvP hs hpt h
  | tick _ _ _ h => exact roOk_tick hs h
  | propose d _ _ _ hh => exact roOk_propose hh hs
  | read d _ hi hbe _ => rw [hnr hi hbe]; exact hs
  | advance _ _ _ _ hno h => exact roOk_adv hs (fun q hq => hqs q hq (hno q hq)) h
  | advP _ _ _ _ _ _ _ h =>
    rcases h with rfl | ⟨-, -, hcs⟩
    · exact hs
    · obtain ⟨peers, -, rfl⟩ := hcs
      exact ⟨hs.1, fun h => by simp [psendMsgs, pbecomeCandidate] at h⟩
  | sends _ _ _ _ h => exact roOk_sends h hs
  | adoptX x _ _ _ _ _ _ => exact ⟨hs.1, fun h => by simp [pbecomeFollower] at h⟩
  | campX x p1 _ _ _ _ _ _ _ hp1 _ hc =>
    obtain ⟨-, peers, -, rfl⟩ := hc
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact ⟨hs.1, fun h => by simp [psendMsgs, pbecomeCandidate] at h⟩

/-! ## The messages -/

/-- What `msgShape.stmt` says of a message to another node, but a heartbeat's context: from the
node but a forwarded read request (which keeps its source's `From`); a heartbeat response's
context the cause's; without reads a heartbeat's none (`c` the cause). -/
def MShape (md : RnMode) (id : w64) (c : Option Msg) (q : Msg) : Prop :=
  (q.ty ≠ .readIndex → q.src = id) ∧ (NetTy md q.ty ∨ q.ty = .propose) ∧ EntsNormal q.entries ∧
  (q.ty = .heartbeatResp → ∃ m, c = some m ∧ m.ty = .heartbeat ∧ q.ctx = m.ctx) ∧
  (md.reads = false → q.ty = .heartbeat → q.ctx = []) ∧ (q.ty = .readIndex → MsgNums (2 ^ 61) q)

/-- Without reads an `MShape` heartbeat or response has no context: a response echoes the handled
heartbeat's, which (on the network) has none (`MsgMask`). -/
theorem mshape_ctx {R : RunCfg} {S : AntCheck.State} {net : List Msg} {id : w64} {c : Option Msg}
    {q : Msg} (hnet : NetOk R S net) (hc : ∀ m, c = some m → m ∈ net) (hq : MShape R.md id c q) :
    R.md.reads = false → (q.ty = .heartbeat ∨ q.ty = .heartbeatResp) → q.ctx = [] := by
  intro hrd hh
  rcases hh with hh | hh
  · exact hq.2.2.2.2.1 hrd hh
  · obtain ⟨m, hcm, hmt, hx⟩ := hq.2.2.2.1 hh
    rw [hx]; exact (hnet.2.2.2.2.1 m (hc m hcm)).2.2.2.1 hrd (.inl hmt)

/-- Every message of `s`'s outbox to another node is `MShape`. -/
def OutShape (md : RnMode) (id : w64) (c : Option Msg) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst ≠ id → MShape md id c q

theorem outShape_nil {id : w64} {c : Option Msg} {s : PState} (h : s.outbox = []) :
    OutShape md id c s := by
  intro q hq; rw [h] at hq; cases hq

/-- Messages queued after `X`'s. -/
theorem outShape_out {id : w64} {c : Option Msg} {X t : PState} {ms : List Msg}
    (hX : OutShape md id c X) (ho : t.outbox = X.outbox ++ ms)
    (hms : ∀ q ∈ ms, q.dst ≠ id → MShape md id c q) : OutShape md id c t := by
  intro q hq hne
  rw [ho] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hX q hq hne
  · exact hms q hq hne

theorem outShape_one {id : w64} {c : Option Msg} {X : PState} {q : Msg} (hX : OutShape md id c X)
    (hq : MShape md id c q) : OutShape md id c (psendMsgs X [q]) :=
  outShape_out hX rfl fun x hx _ => by rw [List.mem_singleton.mp hx]; exact hq

theorem mshape_plain {id d t : w64} {c : Option Msg} {ty : MsgType} {rj : Bool} (hty : NetTy md ty)
    (hne : ty ≠ .heartbeatResp) (hne' : ty ≠ .heartbeat) (hri : ty ≠ .readIndex) :
    MShape md id c (Msg.plain ty id d t rj) :=
  ⟨fun _ => rfl, .inl hty, (fun e he => by simp [Msg.plain] at he), (fun h => absurd h hne),
    (fun _ h => absurd h hne'), fun h => absurd h hri⟩

theorem mshape_mk {id d t ix lt cm rh : w64} {c : Option Msg} {ty : MsgType} {rj : Bool}
    (hty : NetTy md ty) (hne : ty ≠ .heartbeatResp) (hne' : ty ≠ .heartbeat) (hri : ty ≠ .readIndex) :
    MShape md id c (Msg.mk ty id d t rj ix lt cm rh []) :=
  ⟨fun _ => rfl, .inl hty, entsNormal_nil, fun h => absurd h hne, fun _ h => absurd h hne',
    fun h => absurd h hri⟩

/-- An append of the log (`AppOk`). -/
theorem mshape_app {id : w64} {c : Option Msg} {X : PState} {q : Msg} (hl : EntsNormal X.log)
    (h : AppOk id X q) : MShape md id c q :=
  ⟨fun _ => h.2.1, .inl (.inl h.1), fun e he => hl e (h.2.2.2.2.2.2.1 e he),
    (fun h' => by rw [h.1] at h'; cases h'), (fun _ h' => by rw [h.1] at h'; cases h'),
    (fun h' => by rw [h.1] at h'; cases h')⟩

/-- A leader's heartbeat (`HbSendOk`), with no context without reads. -/
theorem mshape_hb {c : CfgM} {id : w64} {cm : Option Msg} {s : PState} {q : Msg}
    (h : HbSendOk c id s q) (hctx : md.reads = false → q.ctx = []) : MShape md id cm q :=
  ⟨fun _ => h.1.2.1, .inl (by simp [NetTy, h.1.1]), by rw [h.2.2.2.1]; exact entsNormal_nil,
    (fun h' => by rw [h.1.1] at h'; cases h'), fun hr _ => hctx hr, (fun h' => by rw [h.1.1] at h'; cases h')⟩

/-- A read request's answer (`RespMsg`) of requests with normal entries; there are some only with
reads (`hrd`). -/
theorem mshape_resp {id T : w64} {cm : Option Msg} {qs : List ReadReq} {q : Msg}
    (h : RespMsg id T qs q) (hrd : md.reads = false → qs = []) (hq : ∀ r ∈ qs, EntsNormal r.ents) :
    MShape md id cm q := by
  obtain ⟨h1, h2, -, -, -, -, -, r, hr, -, -, he⟩ := h
  have hrd' : md.reads = true := by
    cases h' : md.reads
    · rw [hrd h'] at hr; cases hr
    · rfl
  exact ⟨fun _ => h2, .inl (by simp [NetTy, hrd', h1]), by rw [he]; exact hq r hr,
    (fun h' => by rw [h1] at h'; cases h'), (fun _ h' => by rw [h1] at h'; cases h'),
    (fun h' => by rw [h1] at h'; cases h')⟩

theorem outShape_apps {id : w64} {c : Option Msg} {X : PState} {ms : List Msg}
    (hX : OutShape md id c X) (hl : EntsNormal X.log) (hms : ∀ x ∈ ms, x.dst ≠ id → AppOk id X x) :
    OutShape md id c (psendMsgs X ms) :=
  outShape_out hX rfl fun q hq hne => mshape_app hl (hms q hq hne)

theorem outShape_sends {id : w64} {c : Option Msg} {X s' : PState} (hX : OutShape md id c X)
    (hl : EntsNormal s'.log) (h : SendsEnd cf id X s') : OutShape md id c s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact outShape_apps hX hl fun x hx _ => (hms x hx).1

theorem outShape_win {id : w64} {c : Option Msg} {X s' : PState} (hX : OutShape md id c X)
    (hl : EntsNormal s'.log) (h : WinEnd cf id X s') : OutShape md id c s' := by
  obtain ⟨mt, ms, -, hms, rfl⟩ := h
  refine outShape_apps (X := pwinState id X mt) hX hl fun x hx hne => ?_
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
  · exact (hms x hx).1

theorem outShape_propose {id : w64} {c : Option Msg} {X s' : PState} {m : Msg}
    (hX : OutShape md id c X) (hl : EntsNormal s'.log) (hent : EntsNormal m.entries)
    (h : ProposeEnd cf id X m s') : OutShape md id c s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, hms, rfl⟩
    · exact hX
    · refine outShape_apps (X := pappend X _) hX hl fun x hx hne => ?_
      rcases List.mem_append.mp hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
      · exact (hms x hx).1
  · split at h
    · subst h
      exact outShape_one hX ⟨fun _ => rfl, .inr rfl, hent, (fun h => by cases h), (fun _ h => by cases h),
        (fun h => by cases h)⟩
    · subst h; exact hX

/-- A read request's messages (`ReadIdxEnd`, with reads): a leader's heartbeats, its answer (the
request's entries), a forward to the leader. -/
theorem outShape_readIdx {id : w64} {cm : Option Msg} {s s' : PState} {m : Msg}
    (hX : OutShape md id cm s) (hrd : md.reads = true) (hent : EntsNormal m.entries)
    (hnum : MsgNums (2 ^ 61) m) (h : ReadIdxEnd cf id s m s') : OutShape md id cm s' := by
  obtain ⟨ms, -, ho, hms⟩ := readIdxEnd_out h
  refine outShape_out hX ho fun q hq _ => ?_
  rcases hms q hq with ⟨-, hh⟩ | hh | ⟨-, -, rfl⟩
  · exact mshape_hb hh (fun h' => by rw [hrd] at h'; cases h')
  · exact mshape_resp hh (fun h' => by rw [hrd] at h'; cases h')
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hent)
  · exact ⟨fun h' => (h' rfl).elim, .inl (by simp [NetTy, hrd]), hent, (fun h' => by cases h'),
      (fun _ h' => by cases h'), fun _ => hnum⟩

/-- A commit's release (`ReleaseEnd`) after `X`'s messages: heartbeats (none without reads: none is
deferred) and the released requests' answers (their entries normal). -/
theorem outShape_release {c : CfgM} {id : w64} {cm : Option Msg} {X s2 : PState}
    (hX : OutShape md id cm X) (hrd : md.reads = false → RoOk X)
    (hrs : ∀ p ∈ X.rd.pend, EntsNormal p.2) (h : ReleaseEnd c id X s2) : OutShape md id cm s2 := by
  rcases h with ⟨-, hb, hhb, rfl⟩ | ⟨-, rfl⟩
  · refine outShape_out hX rfl fun q hq _ => ?_
    obtain ⟨hhq, k, hk1, hk2, -⟩ := hhb q hq
    refine mshape_hb hhq fun h0 => ?_
    rw [(hrd h0).1] at hk2
    exact absurd (Nat.lt_of_lt_of_le hk1 hk2) (by simp)
  · obtain ⟨ms, -, ho, hms⟩ := preadRespondAll_out id { X with rd := { X.rd with pend := [] } }
      (X.rd.pend.map (fun p => (⟨X.commit, p.1.From', p.2⟩ : ReadReq)))
    refine outShape_out hX ho fun q hq _ =>
      mshape_resp (hms q hq) (fun h0 => by simp [(hrd h0).1]) fun r hr => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact hrs p hp

/-- The type switch's messages after `s`'s (the end log normal): a read request's (with reads,
`hrdm`) with the request's entries; a release's and a read acknowledgement's answers with the
requests' entries (`ReadSrc`), none without reads (`RoOk`); a commit's release's heartbeats, none
without reads (none deferred). -/
theorem outShape_handle {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState} {m : Msg}
    (hX : OutShape md id cm s) (hl : EntsNormal s'.log) (hsc : RdTy m.ty)
    (hent : m.ty = .propose ∨ m.ty = .readIndex → EntsNormal m.entries)
    (hca : m.ty = .heartbeat → cm = some m)
    (hrd : md.reads = false → RoOk s) (hrs : ReadSrc N false s)
    (hrdm : m.ty = .readIndex → md.reads = true) (hnum : m.ty = .readIndex → MsgNums (2 ^ 61) m)
    (h : HandleEnd kk c id s m s') : OutShape md id cm s' := by
  unfold HandleEnd at h
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at h; simp only at h; exact outShape_readIdx hX (hrdm hty) (hent (.inr hty)) (hnum hty) h
  · rw [hty] at h; simp only at h
    split at h
    · rcases h with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hX
    · subst h; exact hX
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact outShape_one hX (mshape_plain (by simp [NetTy]) (by decide) (by decide) (by decide))
    · exact outShape_one hX (mshape_plain (by simp [NetTy]) (by decide) (by decide) (by decide))
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact hX
      · exact outShape_win hX hl hw
      · exact hX
    · subst h; exact hX
  · split at h
    · subst h; exact hX
    · rcases h with ⟨-, rfl⟩ | ⟨-, lastnewi, es', -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩ <;>
        exact outShape_one hX (mshape_mk (by simp [NetTy]) (by decide) (by decide) (by decide))
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩ | ⟨-, x, n, s2, -, -, hrel, hs⟩
      · exact hX
      · exact outShape_sends hX hl hs
      · exact outShape_sends (X := { s with matched := _, commit := n }) hX hl hs
      · refine outShape_sends ?_ hl hs
        refine outShape_release ?_ ?_ ?_ hrel
        · exact hX
        · exact hrd
        · exact fun p hp => (hrs.1 p hp).2 rfl
    · subst h; exact hX
  · split at h
    · subst h; exact hX
    · subst h
      exact outShape_one hX ⟨fun _ => rfl, .inl (by simp [NetTy, Msg.plain]),
        (fun e he => by simp [Msg.plain] at he), (fun _ => ⟨m, hca hty, hty, rfl⟩),
        (fun _ h => by simp [Msg.plain] at h), (fun h => by simp [Msg.plain] at h)⟩
  · split at h
    · rename_i hr
      obtain ⟨s2, hs, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact outShape_sends hX hl hs
      · have hk := readAckEnd_keep ha
        have hs2 : s2.rd = s.rd ∧ s2.role = s.role := by obtain ⟨ms, -, rfl⟩ := hs; exact ⟨rfl, rfl⟩
        obtain ⟨ms, qs, -, ho, hsub, hms⟩ := readAckEnd_out ha
        refine outShape_out (outShape_sends hX (by rw [← hk.log]; exact hl) hs) ho fun q hq _ =>
          mshape_resp (hms q hq) (fun h0 => ?_) fun r hrq => ?_
        · apply List.eq_nil_iff_forall_not_mem.mpr
          intro r hr'
          have := hsub r hr'
          rw [hs2.1, (hrd h0).2 hr] at this; cases this
        · have := hsub r hrq
          rw [hs2.1] at this
          exact (hrs.2 hr r this).2 rfl
    · subst h; exact hX
  · exact outShape_propose hX hl (hent (.inl hty)) h

/-- The invariant of a received message's step and of `Advance`'s: the messages so far, the log
normal, no read request without reads, the requests' sources and entries (`ReadSrc`). -/
def StepShape (md : RnMode) (N : Nat) (id : w64) (cm : Option Msg) (s : PState) : Prop :=
  OutShape md id cm s ∧ EntsNormal s.log ∧ (md.reads = false → RoOk s) ∧ ReadSrc N false s

/-- A received message's step (`RecvEnd`, a type `RdTy`) keeps `StepShape`: the stale
`MsgApp`/`MsgHeartbeat`'s empty answer, the type switch's messages. -/
theorem stepShape_recv {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState} {m : Msg}
    (hI : StepShape md N id cm s) (hsc : RdTy m.ty)
    (hent : m.ty = .app ∨ m.ty = .propose ∨ m.ty = .readIndex → EntsNormal m.entries)
    (hca : m.ty = .heartbeat → cm = some m) (hrdm : m.ty = .readIndex → md.reads = true)
    (hsrc : m.ty = .readIndex → m.src = W64 0 ∨ ∃ j : Fin N, m.src = nodeId j)
    (hnum : m.ty = .readIndex → MsgNums (2 ^ 61) m)
    (h : RecvEnd kk c id s m s') : StepShape md N id cm s' := by
  obtain ⟨hX, hl, hrd, hrs⟩ := hI
  have hl' := entsNormal_recv hsc (fun h' => hent (h'.elim .inl (fun h'' => .inr (.inl h'')))) hl h
  refine ⟨?_, hl', fun h0 => roOk_recv (hrd h0) hsc (fun hty => by
      have := hrdm hty; rw [h0] at this; cases this) h,
    readSrc_recv hrs hsc (fun hty => ⟨hsrc hty, fun _ => hent (.inr (.inr hty))⟩) h⟩
  have hent' : m.ty = .propose ∨ m.ty = .readIndex → EntsNormal m.entries :=
    fun h' => hent (.inr h')
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl | ⟨-, -, rfl⟩ | ⟨hpv, -⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact outShape_handle hX hl' hsc hent' hca hrd hrs hrdm hnum hh
  · exact hX
  · exact outShape_one hX (mshape_mk (by simp [NetTy]) (by decide) (by decide) (by decide))
  · exact absurd (.inl hpv) (not_preTy hsc)
  · exact hX
  · have ho := (preEnd_facts (not_preTy hsc) hpre).1
    refine outShape_handle (N := N) (fun q hq => hX q (ho ▸ hq)) hl' hsc hent' hca ?_ ?_ hrdm hnum hh
    · intro h0
      rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact ⟨(hrd h0).1, fun h => by simp [pbecomeFollower] at h⟩
      · exact hrd h0
      · exact hrd h0
    · rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · exact hrs.nl rfl (by simp [pbecomeFollower])
      · exact hrs
      · exact hrs

/-- `Advance`'s steps (the node's own acknowledgements and votes) keep `StepShape`. -/
theorem stepShape_adv {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState} {qs : List Msg}
    (hI : StepShape md N id cm s) (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp)
    (h : AdvanceEnd kk c id s qs s') : StepShape md N id cm s' := by
  induction h with
  | nil => exact hI
  | cons s s1 s' q qs hr _ ih =>
    refine ih ?_ (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    have hty := hq q (List.mem_cons_self ..)
    have hne : ∀ t : MsgType, q.ty = t → t ≠ .appResp → t ≠ .voteResp → False := fun t ht h1 h2 =>
      hty.elim (fun h => h1 (ht ▸ h)) (fun h => h2 (ht ▸ h))
    refine stepShape_recv hI ?_ (fun h' => ?_) (fun h' => (hne _ h' (by decide) (by decide)).elim)
      (fun h' => (hne _ h' (by decide) (by decide)).elim)
      (fun h' => (hne _ h' (by decide) (by decide)).elim)
      (fun h' => (hne _ h' (by decide) (by decide)).elim) hr
    · rcases hty with h' | h' <;> simp [RdTy, S4Ty, h']
    · rcases h' with h' | h' | h' <;> exact (hne _ h' (by decide) (by decide)).elim

/-- A campaign's messages (`CampaignSends`): its vote requests. -/
theorem outShape_campaignSends {c : CfgM} {id : w64} {cm : Option Msg} {X s' : PState} {cl : List w8}
    (hX : X.outbox = []) (h : CampaignSends c id X cl s') : OutShape md id cm s' := by
  obtain ⟨peers, -, rfl⟩ := h
  intro q hq hne
  rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
  · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
  · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
    exact ⟨fun _ => rfl, .inl (by simp [NetTy, pvoteReq]), (fun e he => by simp [pvoteReq] at he),
      (fun h => by simp [pvoteReq] at h), (fun _ h => by simp [pvoteReq] at h),
      (fun h => by simp [pvoteReq] at h)⟩

/-- A received pre-vote request or response's messages (`recvEnd_pre`): a stale request's
rejection, a request's answer (pre-vote on: the request is on the network, `hpv`), a campaign's
requests. -/
theorem outShape_recvP {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState} {m : Msg}
    (hX : s.outbox = []) (hpv : m.ty = .preVote → md.prevote = true)
    (hty : m.ty = .preVote ∨ m.ty = .preVoteResp) (h : RecvEnd kk c id s m s') :
    OutShape md id cm s' := by
  rcases recvEnd_pre hty h with rfl | ⟨-, hpt, rfl⟩ | ⟨hpt, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, -, rfl⟩ |
      ⟨-, -, -, -, hcs⟩
  · exact outShape_nil hX
  · exact outShape_one (outShape_nil hX) (mshape_plain (by simp [NetTy, hpv hpt]) (by decide) (by decide) (by decide))
  · exact outShape_one (outShape_nil hX) (mshape_plain (by simp [NetTy, hpv hpt]) (by decide) (by decide) (by decide))
  · exact outShape_one (outShape_nil hX) (mshape_plain (by simp [NetTy, hpv hpt]) (by decide) (by decide) (by decide))
  · exact outShape_nil (s := pbecomeFollower s _ _) hX
  · exact outShape_campaignSends hX hcs

/-- A tick's messages (`TickEnd`): a campaign's vote requests, a pre-campaign's pre-vote requests
(pre-vote on at the node, so in the run, `hpv`), a leader's heartbeats (their context `hbCtx` of
the read-only queue, empty without reads: no read request is pending at a leader, `hro`); nothing
at a check-quorum step-down. -/
theorem outShape_tick {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState}
    (hro : md.reads = false → s.role = .leader → s.rd.ro.pending = [])
    (hpv : kk.prevote = true → md.prevote = true) (hX : s.outbox = [])
    (h : TickEnd kk c id s s') : OutShape md id cm s' := by
  rcases h with rfl | ⟨-, -, hce⟩ | ⟨-, hk, -, peers, -, rfl⟩ | ⟨hr, ms, hms, rfl⟩ | ⟨-, -, rfl⟩
  · exact outShape_nil hX
  · exact outShape_campaignSends hX hce.sends
  · intro q hq hne
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
      exact ⟨fun _ => rfl, .inl (by simp [NetTy, hpv hk]), (fun e he => by simp [pvoteReq] at he),
        (fun h => by simp at h), (fun _ h => by simp at h), (fun h => by simp at h)⟩
  · intro q hq _
    obtain ⟨hh, -, -, he, hc, -⟩ := hms q (mem_psend hX hq)
    exact ⟨fun _ => hh.2.1, .inl (by simp [NetTy, hh.1]), (by rw [he]; exact entsNormal_nil),
      (fun h => by rw [hh.1] at h; cases h), fun h0 _ => by rw [hc]; simp [hbCtx, hro h0 hr],
      (fun h => by rw [hh.1] at h; cases h)⟩
  · exact outShape_nil (s := pbecomeFollower s _ _) hX

/-- **The log and the messages along `ReachP`**: the log normal, every message to another node
`MShape` (the cause's context for a heartbeat response). Without reads none is pending (`hrd`), none
is received (`hrdm`) and none is taken (`hnr`: a read request's drain reached the view's own
state); the requests' entries are normal (`hrs`, `hcm`). -/
theorem shape_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView} {ps₁ : PState}
    (hX : v.ps.outbox = []) (hl : EntsNormal v.ps.log)
    (hrd : md.reads = false → RoOk v.ps) (hrs : ReadSrc N false v.ps)
    (hcm : ∀ m, v.cause = some m → EntsNormal m.entries)
    (hcn : ∀ m, v.cause = some m → m.ty = .readIndex → MsgNums (2 ^ 61) m)
    (hpvm : ∀ m ∈ net, m.ty = .preVote → md.prevote = true) (hpvk : kk.prevote = true → md.prevote = true)
    (hrdm : ∀ m ∈ net, m.ty = .readIndex → md.reads = true)
    (hsn : ∀ m ∈ net, ∃ j : Fin N, m.src = nodeId j)
    (hnr : md.reads = false → v.Idle → v.byE = go!"read" → ps₁ = v.ps)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → SelfMsg id v.ps.term q)
    (hr : ReachP kk c id net xnet v ps₁) : EntsNormal ps₁.log ∧ OutShape md id v.cause ps₁ := by
  cases hr with
  | stay _ => exact ⟨hl, outShape_nil hX⟩
  | recv m _ _ _ hca hmn _ _ hty h =>
    obtain ⟨ho, hl', -, -⟩ := stepShape_recv (cm := v.cause) ⟨outShape_nil hX, hl, hrd, hrs⟩ hty
      (fun _ => hcm m hca) (fun _ => hca) (hrdm m hmn) (fun _ => .inr (hsn m hmn)) (hcn m hca) h
    exact ⟨hl', ho⟩
  | recvP m _ _ _ _ hmn _ _ hpt _ h =>
    exact ⟨by rw [(recvPre_keep hpt h).1]; exact hl, outShape_recvP hX (hpvm m hmn) hpt h⟩
  | tick _ _ _ h => exact ⟨entsNormal_tick hl h, outShape_tick (fun h0 => (hrd h0).2) hpvk hX h⟩
  | propose d _ _ _ hh =>
    have hpe : EntsNormal (propMsg id d).entries := by
      intro e he; simp only [propMsg, List.mem_singleton] at he; rw [he]
    have hl' := entsNormal_handle (kk := kk) (.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
      (fun _ => hpe) hl hh
    exact ⟨hl', outShape_propose (outShape_nil hX) hl' hpe hh⟩
  | read d _ hi hbe hh =>
    have hl' : EntsNormal ps₁.log := by rw [(readIdxEnd_keep hh).log]; exact hl
    cases h0 : md.reads
    · rw [hnr h0 hi hbe]; exact ⟨hl, outShape_nil hX⟩
    · exact ⟨hl', outShape_readIdx (outShape_nil hX) h0 (readMsg_normal d) (msgNums_readMsg (by decide) d) hh⟩
  | advance _ _ _ _ hno h =>
    obtain ⟨ho, hl', -, -⟩ := stepShape_adv (cm := v.cause) ⟨outShape_nil hX, hl, hrd, hrs⟩
      (fun q hq => (hqs q hq (hno q hq)).2.2.2.2) h
    exact ⟨hl', ho⟩
  | advP _ _ _ _ _ _ _ h =>
    rcases h with rfl | ⟨-, -, hcs⟩
    · exact ⟨hl, outShape_nil hX⟩
    · exact ⟨by rw [(campaignSends_keep hcs).1]; exact hl, outShape_campaignSends hX hcs⟩
  | sends _ _ _ _ h =>
    have hl' : EntsNormal ps₁.log := by obtain ⟨ms, -, rfl⟩ := h; exact hl
    exact ⟨hl', outShape_sends (outShape_nil hX) hl' h⟩
  | adoptX x _ _ _ _ _ _ => exact ⟨hl, outShape_nil (s := pbecomeFollower v.ps _ _) hX⟩
  | campX x p1 _ _ _ _ _ _ _ hp1 _ hc =>
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact ⟨by rw [(campaignSends_keep hc.sends).1]; exact hl, outShape_campaignSends (by exact hX) hc.sends⟩

/-! ## The ghost prefix along `Reach` -/

/-- A received message other than a snapshot keeps the ghost prefix (`FpNext`'s first arm). -/
theorem recvEndR_fp {Adm : List EntryM → CCState → Prop} {k : NodeK} {id : w64} {r r' : RState}
    {m : Msg} (h : RecvEndR Adm k id r m r') (hne : m.ty ≠ .snap) : r'.fp = r.fp := by
  rcases h.2.2.1 with ⟨-, h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h hne

/-- `Advance` of messages other than snapshots keeps the ghost prefix (the storage
acknowledgements keep it). -/
theorem advanceEndR_fp {Adm : List EntryM → CCState → Prop} {dec : CCDec} {k : NodeK} {id : w64}
    {r r' : RState} {qs : List Msg} (h : AdvanceEndR Adm dec k id r qs r')
    (hq : ∀ q ∈ qs, q.ty ≠ .snap) : r'.fp = r.fp := by
  induction h with
  | nil r r' ha => rcases ha with rfl | ⟨a, -, rfl⟩ | ⟨j, sn, cs', -, rfl⟩ <;> rfl
  | cons r r1 r' q qs hr _ ih =>
    exact (ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))).trans
      (recvEndR_fp hr (hq q (List.mem_cons_self ..)))

/-- `mskB1`'s network types are no snapshot. -/
theorem b1rTy_ne_snap {t : MsgType} (h : B1rTy t) : t ≠ .snap := by
  rcases h with ((h | h | h | h | h | h | h) | h | h) | h | h <;> rw [h] <;> decide

/-- **The ghost prefix is kept along `Reach`** (for the runs a mask below `mskB1` admits: no
snapshot is received). -/
theorem reach_fp {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    r₁.fp = v.r.fp := by
  obtain ⟨-, -, -, -, -, hty⟩ := hin.b1 hmsk
  cases hr with
  | stay _ => rfl
  | input inp _ hinp _ _ _ _ hm _ hs =>
    rcases Input.step_b1 hmsk hinp hs with ⟨m, rfl⟩ | ⟨-, hs⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩ | hx
    · obtain ⟨hmn, -, -⟩ := hm m rfl
      exact recvEndR_fp hs (b1rTy_ne_snap (hty m hmn))
    · exact hs.2.2.1
    · exact recvEndR_fp hs (by simp [propMsg])
    · exact recvEndR_fp hs.2 (by simp [readMsg])
    · exact (inputStep_x_keep hx hs).2.1
  | advance _ _ _ _ _ _ ha _ =>
    refine advanceEndR_fp ha fun q hq => ?_
    rcases (hv.qs q hq).ty3 with h | h | h <;> rw [h] <;> decide

theorem advanceEnd_nil {k : NodeK} {c : CfgM} {id : w64} {s s' : PState}
    (h : AdvanceEnd k c id s [] s') : s' = s := by
  cases h; rfl

/-- **Without reads `ReachIn` takes no read request** (below `mskB1`): a view between inputs whose
drain is a read request's (`go!"read"`) reached its own state, by no input (`stay`) or an empty
`Advance`; a read request is an input only with reads (`InputStep`). -/
theorem reachIn_noRead {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hrd : R.md.reads = false)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) : v.Idle → v.byE = go!"read" → r₁.p = v.ps := by
  intro hi hb
  cases hr with
  | stay _ => rfl
  | input inp _ hinp _ hbe _ _ _ _ hs =>
    rw [hbe] at hb
    rcases Input.step_b1 hmsk hinp hs with ⟨m, rfl⟩ | ⟨hti, -⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩ | ⟨x, rfl⟩ |
        ⟨to, rfl⟩ | ⟨⟨t, rfl⟩, -⟩
    · simp only [Input.byE] at hb; exact absurd hb (by decide)
    · rcases hti with rfl | rfl <;> simp only [Input.byE] at hb <;> exact absurd hb (by decide)
    · simp only [Input.byE] at hb; exact absurd hb (by decide)
    · have := hs.1; rw [hrd] at this; cases this
    all_goals simp only [Input.byE] at hb; exact absurd hb (by decide)
  | advance _ _ _ _ _ _ ha _ =>
    have ha' := advanceEndR_toP ha
    rw [hi.1] at ha'
    exact advanceEnd_nil ha'

/-! ## The shape along `Reach` -/

theorem entsNormal_full {r : RState} (h : EntsNormal r.full) : EntsNormal r.fp ∧ EntsNormal r.p.log :=
  ⟨fun e he => h e (List.mem_append_left _ he), fun e he => h e (List.mem_append_right _ he)⟩

/-- **The log and the messages of the state a `Ready` is taken at** (`shape_reachP`): the full log
normal, every message to another node `MShape` (the cause's context for a heartbeat response). For
the runs a mask below `mskB1` admits (a pre-vote request on the network, or a node's pre-campaign,
with pre-vote on in the run; a read request on it with reads on; without reads none pending,
`NodeFacts.roPend`, and none taken, `reachIn_noRead`; the requests' entries normal,
`NodeFacts.readSrc`, the cause's, `hcm`). -/
theorem shape_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) (hfl : EntsNormal v.r.full)
    (hcm : ∀ m, v.cause = some m → EntsNormal m.entries) :
    EntsNormal r₁.full ∧ OutShape R.md (nodeId n) v.cause r₁.p := by
  obtain ⟨hmd, -⟩ := hin.b1 hmsk
  have hcc : R.md.confChanges = false := by rw [hmd]
  have hfp := reach_fp hmsk hin hv hr
  obtain ⟨hf0, hl⟩ := entsNormal_full hfl
  have hpvm : ∀ m ∈ net, m.ty = .preVote → R.md.prevote = true := fun m hmn hpv => by
    simpa [NetTy, hpv] using (hnet.2.2.2.2.1 m hmn).2.2.1
  have hrdm : ∀ m ∈ net, m.ty = .readIndex → R.md.reads = true := fun m hmn hri => by
    simpa [NetTy, hri] using (hnet.2.2.2.2.1 m hmn).2.2.1
  have hrs : ReadSrc R.N false v.ps := by have h := hv.facts.readSrc; rw [hcc] at h; exact h
  obtain ⟨hl', ho⟩ := shape_reachP hv.facts.outbox hl
    (fun h0 => ⟨hv.facts.pend0 h0, hv.facts.roPend h0⟩) hrs hcm
    (fun m hm => (hnet.2.2.2.2.1 m (hv.cause m hm).1).2.2.2.2) hpvm (R.hpv n) hrdm
    (fun m hmn => by obtain ⟨i, hi, -⟩ := (hnet.1 m hmn).2.1; exact ⟨i, hi⟩)
    (fun h0 => reachIn_noRead hmsk h0 hr)
    (fun q hq hne => (hv.qs q hq).self hne) (ReachIn.toP hmsk hin hnet hv hr)
  have hfull : EntsNormal (r₁.fp ++ r₁.p.log) := entsNormal_append (hfp ▸ hf0) hl'
  exact ⟨hfull, ho⟩

/-! ## The destinations -/

/-- Every member of the configuration `c` is one of the `N` servers. -/
def CfgIn (N : Nat) (c : CfgM) : Prop := ∀ d, d ∈ c.ids → ∃ j : Fin N, d = nodeId j

/-- The initial configuration's members are servers. -/
theorem cfgIn_voters0 (R : RunCfg) : CfgIn R.N (CfgM.simple R.voters0 ∅) := by
  intro d h
  have hv : d ∈ R.voters0 := by
    simp only [CfgM.ids, CfgM.voters, CfgM.simple, GMap.elem_of_union] at h
    rcases h with (h | h) | h
    · exact h
    · exact absurd h (by simp [Membership.mem, GMap.lookup_empty])
    · exact absurd h (by simp [Membership.mem, GMap.lookup_empty])
  unfold RunCfg.voters0 at hv
  rw [elem_of_list_to_set, List.mem_map] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  rw [List.mem_range] at hi
  exact ⟨⟨i, by have := R.hK; omega⟩, rfl⟩

/-- Every message of `s`'s outbox to another node is to one of the `N` servers. -/
def DstIn (N : Nat) (id : w64) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst ≠ id → ∃ j : Fin N, q.dst = nodeId j

theorem dstIn_nil {id : w64} {s : PState} (h : s.outbox = []) : DstIn N id s := by
  intro q hq; rw [h] at hq; cases hq

theorem dstIn_send {id : w64} {s X : PState} {ms : List Msg} (hX : X.outbox = s.outbox)
    (h : DstIn N id s) (hms : ∀ x ∈ ms, x.dst ≠ id → ∃ j : Fin N, x.dst = nodeId j) :
    DstIn N id (psendMsgs X ms) := by
  intro q hq hne
  rw [psendMsgs_outbox, hX] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact h q hq hne
  · exact hms q hq hne

theorem dstIn_one {id d : w64} {s X : PState} {q : Msg} (hX : X.outbox = s.outbox)
    (h : DstIn N id s) (hd : q.dst = d) (hdn : ∃ j : Fin N, d = nodeId j) :
    DstIn N id (psendMsgs X [q]) :=
  dstIn_send hX h fun x hx _ => by rw [List.mem_singleton.mp hx, hd]; exact hdn

theorem dstIn_sends {c : CfgM} {id : w64} {X s' : PState} (hc : CfgIn N c) (h : SendsEnd c id X s')
    (hX : DstIn N id X) : DstIn N id s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact dstIn_send rfl hX fun x hx _ => hc _ (hms x hx).2.2

theorem dstIn_win {c : CfgM} {id : w64} {X s' : PState} (hc : CfgIn N c) (h : WinEnd c id X s')
    (hX : DstIn N id X) : DstIn N id s' := by
  obtain ⟨mt, ms, -, hms, rfl⟩ := h
  refine dstIn_send rfl hX fun x hx hne => ?_
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
  · exact hc _ (hms x hx).2.2

theorem dstIn_propose {c : CfgM} {id : w64} {X s' : PState} {m : Msg} (hc : CfgIn N c)
    (hl : LeadIn N X) (h : ProposeEnd c id X m s') (hX : DstIn N id X) : DstIn N id s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, hms, rfl⟩
    · exact hX
    · refine dstIn_send rfl hX fun x hx hne => ?_
      rcases List.mem_append.mp hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
      · exact hc _ (hms x hx).2.2
  · split at h
    · rename_i hc'
      subst h
      exact dstIn_one rfl hX rfl (hl.resolve_left hc'.2)
    · subst h; exact hX

/-- Messages queued after `s`'s, to servers. -/
theorem dstIn_out {id : w64} {s t : PState} {ms : List Msg} (h : DstIn N id s)
    (ho : t.outbox = s.outbox ++ ms) (hms : ∀ x ∈ ms, x.dst ≠ id → ∃ j : Fin N, x.dst = nodeId j) :
    DstIn N id t := by
  intro q hq hne
  rw [ho] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact h q hq hne
  · exact hms q hq hne

/-- A read request's answer goes to the request's source, a server (neither `0` nor the node). -/
theorem dst_resp {id T : w64} {qs : List ReadReq} {q : Msg} (h : RespMsg id T qs q)
    (hq : ∀ r ∈ qs, r.src = W64 0 ∨ ∃ j : Fin N, r.src = nodeId j) : ∃ j : Fin N, q.dst = nodeId j := by
  obtain ⟨-, -, -, -, h0, -, -, r, hr, hd, -⟩ := h
  rw [hd]; exact (hq r hr).resolve_left (fun h' => h0 (hd.trans h'))

/-- A read request's messages (`ReadIdxEnd`): a leader's heartbeats to the configuration's peers,
the answer to the request's source, a forward to the leader hint. -/
theorem dstIn_readIdx {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hc : CfgIn N c)
    (hX : DstIn N id s) (hl : LeadIn N s) (hsrc : m.src = W64 0 ∨ ∃ j : Fin N, m.src = nodeId j)
    (h : ReadIdxEnd c id s m s') : DstIn N id s' := by
  obtain ⟨ms, -, ho, hms⟩ := readIdxEnd_out h
  refine dstIn_out hX ho fun q hq _ => ?_
  rcases hms q hq with ⟨-, hh⟩ | hh | ⟨-, hld, rfl⟩
  · exact hc _ hh.2.2.2.2
  · exact dst_resp hh fun r hr => by rw [List.mem_singleton.mp hr]; exact hsrc
  · exact hl.resolve_left hld

/-- A commit's release: heartbeats to the configuration's peers, the answers to the deferred
requests' sources. -/
theorem dstIn_release {c : CfgM} {id : w64} {X s2 : PState} (hc : CfgIn N c) (hX : DstIn N id X)
    (hrs : ∀ p ∈ X.rd.pend, p.1.From' = W64 0 ∨ ∃ j : Fin N, p.1.From' = nodeId j)
    (h : ReleaseEnd c id X s2) : DstIn N id s2 := by
  obtain ⟨ms, -, ho, hms⟩ := releaseEnd_out h
  refine dstIn_out hX ho fun q hq _ => ?_
  rcases hms q hq with hh | hh
  · exact hc _ hh.2.2.2.2
  · refine dst_resp hh fun r hr => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact hrs p hp

/-- The type switch's messages go to the sender (a server), a leader's appends and heartbeats to
the configuration's peers, a forwarded proposal or read request to the leader (a server,
`LeadIn`), a read request's answer to its source (`ReadSrc`). -/
theorem dstIn_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} {cc : Bool} (hc : CfgIn N c)
    (hX : DstIn N id s) (hl : LeadIn N s) (hrs : ReadSrc N cc s) (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hsc : RdTy m.ty) (h : HandleEnd kk c id s m s') : DstIn N id s' := by
  unfold HandleEnd at h
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at h; simp only at h; exact dstIn_readIdx hc hX hl (.inr hsn) h
  · rw [hty] at h; simp only at h
    split at h
    · rcases h with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hX
    · subst h; exact hX
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact dstIn_one rfl hX rfl hsn
    · exact dstIn_one rfl hX rfl hsn
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact hX
      · exact dstIn_win hc hw hX
      · exact hX
    · subst h; exact hX
  · split at h
    · subst h; exact hX
    · rcases h with ⟨-, rfl⟩ | ⟨-, lastnewi, es', -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩
      · exact dstIn_one rfl hX rfl hsn
      · exact dstIn_one rfl hX rfl hsn
      · exact dstIn_one rfl hX rfl hsn
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩ | ⟨-, x, n, s2, -, -, hrel, hs⟩
      · exact hX
      · exact dstIn_sends hc hs hX
      · exact dstIn_sends hc hs hX
      · refine dstIn_sends hc hs ?_
        refine dstIn_release hc ?_ ?_ hrel
        · exact hX
        · exact fun p hp => (hrs.1 p hp).1
    · subst h; exact hX
  · split at h
    · subst h; exact hX
    · subst h; exact dstIn_one rfl hX rfl hsn
  · split at h
    · rename_i hr
      obtain ⟨s2, hs, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact dstIn_sends hc hs hX
      · have hs2 : s2.rd = s.rd := by obtain ⟨ms, -, rfl⟩ := hs; rfl
        obtain ⟨ms, qs, -, ho, hsub, hms⟩ := readAckEnd_out ha
        refine dstIn_out (dstIn_sends hc hs hX) ho fun q hq _ => dst_resp (hms q hq) fun r hrq => ?_
        have := hsub r hrq
        rw [hs2] at this
        exact (hrs.2 hr r this).1
    · subst h; exact hX
  · exact dstIn_propose hc hl h hX

theorem dstIn_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} {cc : Bool} (hc : CfgIn N c)
    (hX : DstIn N id s) (hl : LeadIn N s) (hrs : ReadSrc N cc s) (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hsc : RdTy m.ty) (h : RecvEnd kk c id s m s') : DstIn N id s' := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl | ⟨-, -, rfl⟩ | ⟨hpv, -⟩⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact dstIn_handle hc hX hl hrs hsn hsc hh
  · exact hX
  · exact dstIn_one rfl hX rfl hsn
  · exact absurd (.inl hpv) (not_preTy hsc)
  · exact hX
  · have hk := not_preTy hsc
    have ho := (preEnd_facts hk hpre).1
    have hpre' : s1 = pbecomeFollower s m.term (if fromLeader m.ty then m.src else W64 0) ∨ s1 = s := by
      rcases hpre with ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, hpk, -⟩
      · exact .inl h
      · exact .inr h
      · exact absurd hpk hk
    have hl1 : LeadIn N s1 := by
      rcases hpre' with rfl | rfl
      · show (if fromLeader m.ty then m.src else W64 0) = W64 0 ∨
          ∃ j : Fin N, (if fromLeader m.ty then m.src else W64 0) = nodeId j
        split
        · exact .inr hsn
        · exact .inl rfl
      · exact hl
    have hrs1 : ReadSrc N cc s1 := by
      rcases hpre' with rfl | rfl
      · exact hrs.nl rfl (by simp [pbecomeFollower])
      · exact hrs
    exact dstIn_handle hc (fun q hq => hX q (ho ▸ hq)) hl1 hrs1 hsn hsc hh

/-- `Advance`'s steps (the node's own acknowledgements and vote responses) keep `DstIn`, the
leader hint and `ReadSrc`. -/
theorem dstIn_adv {c : CfgM} {R : RunCfg} {n : Fin R.N} {s s' : PState} {qs : List Msg} {cc : Bool}
    (hc : CfgIn R.N c) (hX : DstIn R.N (nodeId n) s) (hl : LeadHint R.N (nodeId n) s)
    (hrs : ReadSrc R.N cc s)
    (hq : ∀ q ∈ qs, (q.ty = .appResp ∨ q.ty = .voteResp) ∧ q.src = nodeId n)
    (ha : AdvanceEnd kk c (nodeId n) s qs s') : DstIn R.N (nodeId n) s' := by
  induction ha with
  | nil => exact hX
  | cons s s1 s' q qs hr _ ih =>
    have hq0 := hq q (List.mem_cons_self ..)
    have hsc : RdTy q.ty := by rcases hq0.1 with h0 | h0 <;> simp [RdTy, S4Ty, h0]
    have hnr : q.ty = .readIndex → False := fun h' => by
      rcases hq0.1 with h0 | h0 <;> rw [h0] at h' <;> cases h'
    exact ih (dstIn_recv hc hX hl.2 hrs ⟨n, hq0.2⟩ hsc hr)
      (leadHint_recv hl (nodeId_ne_zero n) ⟨n, rfl⟩ hsc (.inr (hq0.1.elim .inl (fun h => .inr (.inl h))))
        ⟨n, hq0.2⟩ hr)
      (readSrc_recv hrs hsc (fun h' => (hnr h').elim) hr)
      (fun x hx => hq x (List.mem_cons_of_mem _ hx))

/-- A campaign's vote requests go to the configuration's voters. -/
theorem dstIn_campaignSends {c : CfgM} {id : w64} {X s' : PState} {cl : List w8} (hc : CfgIn N c)
    (hX : X.outbox = []) (h : CampaignSends c id X cl s') : DstIn N id s' := by
  obtain ⟨peers, hp, rfl⟩ := h
  intro q hq hne
  rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
  · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    have hd' : d ∈ elements (c.voters \ {[id]}) := hp.mem_iff.mp hd
    rw [GMap.elem_of_elements, GMap.elem_of_difference] at hd'
    exact hc _ ((GMap.elem_of_union _ _ _).2 (.inl hd'.1))

/-- A received pre-vote request or response's answers go to the sender (a server), a campaign's
requests to the voters. -/
theorem dstIn_recvP {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hc : CfgIn N c)
    (hX : s.outbox = []) (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hty : m.ty = .preVote ∨ m.ty = .preVoteResp) (h : RecvEnd kk c id s m s') :
    DstIn N id s' := by
  rcases recvEnd_pre hty h with rfl | ⟨-, -, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, -, rfl⟩ |
      ⟨-, -, -, -, hcs⟩
  · exact dstIn_nil hX
  · exact dstIn_one rfl (dstIn_nil hX) rfl hsn
  · exact dstIn_one rfl (dstIn_nil hX) rfl hsn
  · exact dstIn_one rfl (dstIn_nil hX) rfl hsn
  · exact dstIn_nil (s := pbecomeFollower s _ _) hX
  · exact dstIn_campaignSends hc hX hcs

/-- A tick's messages: a campaign's vote requests and a pre-campaign's pre-vote requests to the
configuration's voters, a leader's heartbeats to its peers. -/
theorem dstIn_tick {c : CfgM} {id : w64} {s s' : PState} (hc : CfgIn N c) (hX : s.outbox = [])
    (h : TickEnd kk c id s s') : DstIn N id s' := by
  rcases h with rfl | ⟨-, -, hce⟩ | ⟨-, -, -, peers, hp, rfl⟩ | ⟨-, ms, hms, rfl⟩ | ⟨-, -, rfl⟩
  · exact dstIn_nil hX
  · exact dstIn_campaignSends hc hX hce.sends
  · intro q hq hne
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have hd' : d ∈ elements (c.voters \ {[id]}) := hp.mem_iff.mp hd
      rw [GMap.elem_of_elements, GMap.elem_of_difference] at hd'
      exact hc _ ((GMap.elem_of_union _ _ _).2 (.inl hd'.1))
  · intro q hq _
    exact hc _ (hms q (mem_psend hX hq)).2.2.2.2.2
  · exact dstIn_nil (s := pbecomeFollower s _ _) hX

/-- **The destinations along `ReachP`**: every message to another node is to a server (a read
request's answer to its source, `ReadSrc`). -/
theorem dst_reachP {R : RunCfg} {n : Fin R.N} {c : CfgM} {net : List Msg} {xnet : List XMsg} {v : NodeView}
    {ps₁ : PState} {cc : Bool} (hc : CfgIn R.N c) (hX : v.ps.outbox = [])
    (hlo : LeadHint R.N (nodeId n) v.ps) (hrs : ReadSrc R.N cc v.ps)
    (hsn : ∀ m ∈ net, ∃ j : Fin R.N, m.src = nodeId j)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → (q.ty = .appResp ∨ q.ty = .voteResp) ∧ q.src = nodeId n)
    (hr : ReachP kk c (nodeId n) net xnet v ps₁) : DstIn R.N (nodeId n) ps₁ := by
  cases hr with
  | stay _ => exact dstIn_nil hX
  | recv m _ _ _ _ hmn _ _ hty h => exact dstIn_recv hc (dstIn_nil hX) hlo.2 hrs (hsn m hmn) hty h
  | recvP m _ _ _ _ hmn _ _ hpt _ h => exact dstIn_recvP hc hX (hsn m hmn) hpt h
  | tick _ _ _ h => exact dstIn_tick hc hX h
  | propose d _ _ _ hh => exact dstIn_propose hc hlo.2 hh (dstIn_nil hX)
  | read d _ _ _ hh => exact dstIn_readIdx hc (dstIn_nil hX) hlo.2 (.inl rfl) hh
  | advance _ _ _ _ hno h =>
    exact dstIn_adv hc (dstIn_nil hX) hlo hrs (fun q hq => hqs q hq (hno q hq)) h
  | advP _ _ _ _ _ _ _ h =>
    rcases h with rfl | ⟨-, -, hcs⟩
    · exact dstIn_nil hX
    · exact dstIn_campaignSends hc hX hcs
  | sends _ _ _ _ h => exact dstIn_sends hc h (dstIn_nil hX)
  | adoptX x _ _ _ _ _ _ => exact dstIn_nil (s := pbecomeFollower v.ps _ _) hX
  | campX x p1 _ _ _ _ _ _ _ hp1 _ h' =>
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact dstIn_campaignSends hc (by exact hX) h'.sends

/-- **The destinations of the messages of the state a `Ready` is taken at** (`dst_reachP`): every
one to another node is to a server. For the runs a mask below `mskB1` admits (the initial
configuration). -/
theorem dst_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) : DstIn R.N (nodeId n) r₁.p := by
  obtain ⟨hmd, -⟩ := hin.b1 hmsk
  have hc : CfgIn R.N v.r.cfg.cfg := by
    rw [(hv.facts.conf0 (by rw [hmd])).1]; exact cfgIn_voters0 R
  refine dst_reachP hc hv.facts.outbox hv.leadOk hv.facts.readSrc
    (fun m hmn => by obtain ⟨i, hi, -⟩ := (hnet.1 m hmn).2.1; exact ⟨i, hi⟩)
    (fun q hq hne => ?_) (ReachIn.toP hmsk hin hnet hv hr)
  obtain ⟨h1, -, -, -, h5⟩ := (hv.qs q hq).self hne
  exact ⟨h5, h1⟩

/-- **`msgShape.stmt` but a heartbeat's context** (the `Ready`'s messages are the outbox's to other
nodes, `ReadyOutP`): the full log normal; every message to another node from the node (but a
forwarded read request), of a type the network carries or a proposal, its entries normal, a
heartbeat response's context the handled heartbeat's, without reads a heartbeat's none. -/
theorem msgShape_core {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {ms : List Msg}
    (hin : InMask msk R net xnet) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁)
    (hmsg : ms.Perm (r₁.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n))))
    (hfl : EntsNormal v.r.full) (hcm : ∀ m, v.cause = some m → EntsNormal m.entries) :
    EntsNormal r₁.full ∧ ∀ q ∈ ms, MShape R.md (nodeId n) v.cause q := by
  obtain ⟨hl', ho⟩ := shape_reach hmsk hin hnet hv hr hfl hcm
  refine ⟨hl', fun q hq => ?_⟩
  have hq' := (hmsg.mem_iff).mp hq
  rw [List.mem_filter] at hq'
  exact ho q hq'.1 (of_decide_eq_true hq'.2)

/-- **`msgShape.stmt`'s conclusion over `ReachIn`**, for the runs a mask below `mskB1` admits: a
heartbeat response echoes the handled heartbeat's context, `[]` without reads by the premise; the
destinations by `dst_reach`. -/
theorem msgShape_in_of {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {rd : ReadyD}
    (hin : InMask msk R net xnet) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁)
    (hmsg : (rd.msgs ++ rd.resp).Perm (r₁.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n))))
    (hfl : EntsHarness v.r.full)
    (hcm : ∀ m, v.cause = some m → EntsHarness m.entries ∧
      (R.md.reads = false → m.ty = .heartbeat → m.ctx = [])) :
    EntsHarness r₁.full ∧ (∀ q ∈ rd.msgs ++ rd.resp, ReadyMsgShape R.md (nodeId n) q) ∧
      ReadyMsgsToVoters R.N rd := by
  obtain ⟨hl', hq⟩ := msgShape_core hmsk hin hnet hv hr hmsg hfl (fun m h => (hcm m h).1)
  have hds := dst_reach hmsk hin hnet hv hr
  refine ⟨hl', fun q hmem => ?_, fun q hmem => ?_⟩
  rotate_left
  · have hq' := (hmsg.mem_iff).mp hmem
    rw [List.mem_filter] at hq'
    exact hds q hq'.1 (of_decide_eq_true hq'.2)
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hq q hmem
  refine ⟨h1, h2, fun hrd hh => ?_, h3⟩
  rcases hh with hh | hh
  · exact h5 hrd hh
  · obtain ⟨m, hc, hmt, hx⟩ := h4 hh
    rw [hx]; exact (hcm m hc).2 hrd hmt

/-- **`msgShape.stmt` over `ReachIn`**, for the runs a mask below `mskB1` admits
(`msgShape_in_of`). -/
theorem msgShape_in (msk : SimMask) (hmsk : msk ≤ mskB1) :
    ∀ (R : RunCfg) (dec : CCDec) (Adm : List EntryM → CCState → Prop) (S : AntCheck.State)
      (net : List Msg) (xnet : List XMsg) (n : Fin R.N) (v : NodeView) (r₁ : RState)
      (rd : ReadyD),
      InMask msk R net xnet →
      NetOk R S net → NodeOk R dec S net n v → ReachIn msk R dec Adm net xnet n v r₁ →
      (rd.msgs ++ rd.resp).Perm (r₁.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n))) →
      EntsHarness v.r.full →
      (∀ m, v.cause = some m → EntsHarness m.entries ∧ (R.md.reads = false → m.ty = .heartbeat → m.ctx = [])) →
      EntsHarness r₁.full ∧ (∀ q ∈ rd.msgs ++ rd.resp, ReadyMsgShape R.md (nodeId n) q) ∧
      ReadyMsgsToVoters R.N rd := by
  intro R dec Adm S net xnet n v r₁ rd hin hnet hv hr hmsg hfl hcm
  exact msgShape_in_of hmsk hin hnet hv hr hmsg hfl hcm

/-! ## What `Reach` keeps (the masks below `mskB1`) -/

/-- **Without reads no read request is pending along `Reach`** (`NodeFacts.roPend` at the state a
`Ready` is taken at, `roOk_reachP`): none is on the network (`MsgMask`) or taken
(`reachIn_noRead`). For the runs a mask below `mskB1` admits. -/
theorem reach_roOk {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    R.md.reads = false → RoOk r₁.p := by
  intro hrd
  have hnrm : ∀ m ∈ net, m.ty ≠ .readIndex := fun m hmn hri => by
    have := (hnet.2.2.2.2.1 m hmn).2.2.1
    simp [NetTy, hri, hrd] at this
  exact roOk_reachP ⟨hv.facts.pend0 hrd, hv.facts.roPend hrd⟩
    (fun q hq hne => ((hv.qs q hq).self hne).2.2.2.2) hnrm (reachIn_noRead hmsk hrd hr)
    (ReachIn.toP hmsk hin hnet hv hr)

/-- A received message other than a snapshot keeps the configuration, the ghost prefix and the
restored flag. -/
theorem recvEndR_keep {Adm : List EntryM → CCState → Prop} {k : NodeK} {id : w64} {r r' : RState}
    {m : Msg} (h : RecvEndR Adm k id r m r') (hne : m.ty ≠ .snap) :
    r'.cfg = r.cfg ∧ r'.fp = r.fp ∧ r'.snap = r.snap := by
  refine ⟨h.2.1.2.2, ?_⟩
  rcases h.2.2.1 with ⟨-, h1, h2⟩ | ⟨h, -⟩
  · exact ⟨h1, h2⟩
  · exact absurd h hne

theorem advanceNoSnap_keep {Adm : List EntryM → CCState → Prop} {dec : CCDec} {k : NodeK}
    {id : w64} {r r' : RState} {qs : List Msg} (h : AdvanceNoSnap Adm dec k id r qs r')
    (hq : ∀ q ∈ qs, q.ty ≠ .snap) : r'.cfg = r.cfg ∧ r'.fp = r.fp ∧ r'.snap = r.snap := by
  induction h with
  | nil r r' ha => rcases ha with rfl | ⟨a, -, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  | cons r r1 r' q qs hr _ ih =>
    obtain ⟨a1, a2, a3⟩ := ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    obtain ⟨b1, b2, b3⟩ := recvEndR_keep hr (hq q (List.mem_cons_self ..))
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩

/-- **`Reach` keeps the configuration, the ghost prefix and the restored flag**, and starts with
nothing pending. -/
theorem reach_keep {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    (r₁.cfg = v.r.cfg ∧ r₁.fp = v.r.fp ∧ r₁.snap = v.r.snap) ∧ v.pend = [] ∧ v.xpend = [] := by
  obtain ⟨hmd, -, -, -, -, hty⟩ := hin.b1 hmsk
  cases hr with
  | stay hi => exact ⟨⟨rfl, rfl, rfl⟩, hi.2.1, hi.2.2.1⟩
  | input inp _ hinp hi _ _ _ hm _ hst =>
    refine ⟨?_, hi.2.1, hi.2.2.1⟩
    rcases Input.step_b1 hmsk hinp hst with ⟨m, rfl⟩ | ⟨-, hst⟩ | ⟨d, rfl⟩ | ⟨d, rfl⟩ | hx
    · obtain ⟨hmn, -, -⟩ := hm m rfl
      exact recvEndR_keep hst (b1rTy_ne_snap (hty m hmn))
    · exact ⟨hst.2.1.2.2, hst.2.2.1, hst.2.2.2.1⟩
    · exact recvEndR_keep hst (by simp [propMsg])
    · exact recvEndR_keep hst.2 (by simp [readMsg])
    · exact inputStep_x_keep hx hst
  | advance _ hp hxp _ _ _ _ hns =>
    refine ⟨advanceNoSnap_keep (hns (by rw [hmd])) fun q hq => ?_, hp, hxp⟩
    rcases (hv.qs q hq).ty3 with h | h | h <;> rw [h] <;> decide

/-- **The `Ready`'s messages to other nodes are `PendOk` at the view after it**
(`NodeView.drainOf`, sync), each to a voter (`ReadyOutP`'s `ReadyMsgsToVoters`). -/
theorem pendOk_of_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {rd : ReadyD}
    (hin : InMask msk R net xnet) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) (hro : ReadyOutP R n v r₁ rd) :
    ∀ q ∈ rd.msgs, PendOk R.N (nodeId n) (v.drainOf r₁ rd) q := by
  intro q hq
  have hasync : R.md.async = false := by rw [(hin.b1 hmsk).1]
  have hq' := (((hro.2.2.2.2.2.2.2.2.1 hasync).2).mem_iff).mp hq
  rw [List.mem_filter] at hq'
  have hne : q.dst ≠ nodeId n := of_decide_eq_true hq'.2
  exact PendOk.congr (v := v.withP r₁.p) rfl rfl rfl rfl rfl rfl rfl rfl rfl (reach_keep hmsk hin hv hr).1.1
    (outOk_reach hmsk hin hnet hv hr q hq'.1 hne (hro.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 q (List.mem_append_left _ hq)))

/-- Without conf entries, no conf entry's index (`lastConfIdx` is `0`). -/
theorem lastConfIdx_normal {l : List EntryM} (h : EntsNormal l) (k : Nat) : lastConfIdx l k = 0 := by
  have h1 : ¬ (W32 0 = W32 1) := by decide
  have h2 : ¬ (W32 0 = W32 2) := by decide
  unfold lastConfIdx
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    split
    · rename_i e he
      have he0 : e.Type' = W32 0 := h e (List.mem_of_getElem? he)
      rw [if_neg]
      intro hc; rcases hc with hc | hc <;> rw [he0] at hc
      · exact h1 hc
      · exact h2 hc
    · rfl

end shape

end AntSim
end EtcdGrove
end Perennial
