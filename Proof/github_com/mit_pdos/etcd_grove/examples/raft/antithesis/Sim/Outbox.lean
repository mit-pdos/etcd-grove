/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: a `Ready`'s messages are `PendOk` (#33 S4)

`pendOk_of_reach`: every message a `Ready` hands to another node, taken at the state `ps₁` the
node reached (`Reach`: no input, one input, or `Advance` of the previous `Ready`'s self-addressed
messages), is what the binding's `Send` checks of it (`PendOk`) at the view after the `Ready`
(`NodeView.afterReady`). The outbox is empty at the view (C1), and `InputEnd` queues only at the
state after the preamble: a single input's messages are judged at its end state; `Advance`'s are a
leader's `MsgApp`s, judged at the state they were sent at, which later self-acknowledgements change
only in `Match` and the commit index (so they are `AppOk` at the end, what `PendOk` asks of an
append). Shared by `antSim_quiet` and `antSim_ready`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Scope
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Init

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap

section outbox
variable [GooseExts]
variable {cf : CfgM} {N : Nat} {kk : NodeK} {cc : Bool}

/-- The view `w` with raft's protocol state `s`. -/
def NodeView.withP (w : NodeView) (s : PState) : NodeView := { w with r := { w.r with p := s } }

/-- **`QsOk` with pre-vote off** (no self pre-vote): the S4 shape, a self-acknowledgement or a
self-vote at the node's term. -/
theorem QsOk.old {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (h : QsOk R S n v q) (hk : (R.k n).prevote = false) :
    q.src = nodeId n ∧ q.dst = nodeId n ∧ q.term = v.ps.term ∧ q.reject = false ∧
    ((q.ty = .appResp ∧ v.ps.role = .leader ∧
        AckIn S (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z v.ps.term) (uint.Z q.index)) ∨
     (q.ty = .voteResp ∧
        { voter := nameOf (nodeId n), term := uint.Z v.ps.term, cand := nameOf (nodeId n) } ∈ S.votes)) := by
  obtain ⟨h1, h2, h3, ⟨h4, h5⟩ | ⟨-, -, -, h6, -⟩⟩ := h
  · exact ⟨h1, h2, h4, h3, h5⟩
  · rw [hk] at h6; cases h6

/-! ## `PendOk` per message type -/

/-- `PendOk` reads only the view's role, term, vote, log, base, commit, `Match`, `by` and cause. -/
theorem PendOk.congr {id : w64} {v w : NodeView} {q : Msg} (hr : w.ps.role = v.ps.role)
    (ht : w.ps.term = v.ps.term) (hv : w.ps.vote = v.ps.vote) (hl : w.ps.log = v.ps.log)
    (hb : w.ps.base = v.ps.base) (hc : w.ps.commit = v.ps.commit)
    (hm : w.ps.matched = v.ps.matched) (hbe : w.byE = v.byE) (hca : w.cause = v.cause)
    (hcf : w.r.cfg = v.r.cfg) (h : PendOk N id v q) : PendOk N id w q := by
  unfold PendOk AppOk HeartbeatOk matchOf at *
  rw [hr, ht, hv, hl, hb, hc, hm, hbe, hca, hcf]; exact h

theorem pendOk_app {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin N, q.dst = nodeId j) (hr : w.ps.role = .leader) (ha : AppOk id w.ps q) :
    PendOk N id w q := by
  have hty : q.ty = .app := ha.1
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hr, ha⟩

theorem pendOk_vote {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin N, q.dst = nodeId j) (hty : q.ty = .vote) (hs : q.src = id)
    (hr : w.ps.role = .candidate) (ht : q.term = w.ps.term) (hv : w.ps.vote = id)
    (hi : q.index = (plogLast w.ps.base w.ps.log).index')
    (hlt : q.logterm = (plogLast w.ps.base w.ps.log).term') : PendOk N id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, hr, ht, hv, hi, hlt⟩

theorem pendOk_voteResp {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin N, q.dst = nodeId j) (hty : q.ty = .voteResp) (hs : q.src = id)
    (ht : q.term = w.ps.term) (hv : q.reject = false → w.ps.vote = q.dst) : PendOk N id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, ht, hv⟩

theorem pendOk_heartbeatResp {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin N, q.dst = nodeId j) (hty : q.ty = .heartbeatResp) (hs : q.src = id)
    (ht : q.term = w.ps.term) : PendOk N id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, ht⟩

theorem pendOk_propose {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin N, q.dst = nodeId j) (hty : q.ty = .propose) (hs : q.src = id)
    (ht : q.term = W64 0) : PendOk N id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, ht⟩

theorem pendOk_heartbeat {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin N, q.dst = nodeId j) (hr : w.ps.role = .leader) (hh : HeartbeatOk id w.ps q)
    (hi : q.index = W64 0) (hlt : q.logterm = W64 0) (he : q.entries = []) : PendOk N id w q := by
  have hty : q.ty = .heartbeat := hh.1
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hr, hh, hi, hlt, he⟩

/-! ## One input's messages, judged at its end state -/

/-- Every message to another voter in `s`'s outbox is `PendOk` at the view `w` moved to `s`. -/
def OutOk (N : Nat) (id : w64) (w : NodeView) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst ≠ id → (∃ j : Fin N, q.dst = nodeId j) → PendOk N id (w.withP s) q

theorem outOk_nil {id : w64} {w : NodeView} {s : PState} (h : s.outbox = []) : OutOk N id w s := by
  intro q hq; rw [h] at hq; cases hq

theorem mem_psend {X : PState} {ms : List Msg} {q : Msg} (hX : X.outbox = [])
    (hq : q ∈ (psendMsgs X ms).outbox) : q ∈ ms := by
  rw [psendMsgs_outbox, hX, List.nil_append] at hq; exact hq

/-! ### What the read arms change: the outbox and the read state only -/

/-- `t` is `s` but for its outbox and read state (what queuing messages, deferring, queuing or
answering a read request change). -/
def PKeep (s t : PState) : Prop := t = { s with outbox := t.outbox, rd := t.rd }

theorem pkeep_psend (s : PState) (ms : List Msg) : PKeep s (psendMsgs s ms) := rfl

theorem pkeep_rd (s : PState) (rd : RdState) : PKeep s { s with rd := rd } := rfl

theorem PKeep.trans {s t u : PState} (h1 : PKeep s t) (h2 : PKeep t u) : PKeep s u := by
  unfold PKeep at *
  exact h2.trans (by rw [h1])

theorem PKeep.eq {s t : PState} (h : PKeep s t) : t = { s with outbox := t.outbox, rd := t.rd } := h
theorem PKeep.role {s t : PState} (h : PKeep s t) : t.role = s.role := by
  have := congrArg PState.role h.eq; exact this
theorem PKeep.term {s t : PState} (h : PKeep s t) : t.term = s.term := by
  have := congrArg PState.term h.eq; exact this
theorem PKeep.vote {s t : PState} (h : PKeep s t) : t.vote = s.vote := by
  have := congrArg PState.vote h.eq; exact this
theorem PKeep.lead {s t : PState} (h : PKeep s t) : t.lead = s.lead := by
  have := congrArg PState.lead h.eq; exact this
theorem PKeep.log {s t : PState} (h : PKeep s t) : t.log = s.log := by
  have := congrArg PState.log h.eq; exact this
theorem PKeep.base {s t : PState} (h : PKeep s t) : t.base = s.base := by
  have := congrArg PState.base h.eq; exact this
theorem PKeep.commit {s t : PState} (h : PKeep s t) : t.commit = s.commit := by
  have := congrArg PState.commit h.eq; exact this
theorem PKeep.matched {s t : PState} (h : PKeep s t) : t.matched = s.matched := by
  have := congrArg PState.matched h.eq; exact this

theorem PKeep.pendOk {id : w64} {w : NodeView} {s t : PState} {q : Msg} (h : PKeep s t)
    (hq : PendOk N id (w.withP s) q) : PendOk N id (w.withP t) q :=
  PendOk.congr (v := w.withP s) (w := w.withP t) (h.role) (h.term) (h.vote)
    (h.log) (h.base) (h.commit)
    (h.matched) rfl rfl rfl hq

theorem OutOk.keep {id : w64} {w : NodeView} {s t : PState} {ms : List Msg} (h : OutOk N id w s)
    (hk : PKeep s t) (ho : t.outbox = s.outbox ++ ms)
    (hms : ∀ q ∈ ms, q.dst ≠ id → (∃ j : Fin N, q.dst = nodeId j) → PendOk N id (w.withP t) q) :
    OutOk N id w t := by
  intro q hq hne hd
  rw [ho] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hk.pendOk (h q hq hne hd)
  · exact hms q hq hne hd

/-- A read request's answer (`preadRespond`'s `MsgReadIndexResp`): from the node at the term `T`, to
the source of one of the requests `qs` (neither `0` nor the node: those are answered locally),
carrying its index and entries. -/
def RespMsg (id T : w64) (qs : List ReadReq) (q : Msg) : Prop :=
  q.ty = .readIndexResp ∧ q.src = id ∧ q.term = T ∧ q.dst ≠ id ∧ q.dst ≠ W64 0 ∧
    q.logterm = W64 0 ∧ q.commit = W64 0 ∧
    ∃ r ∈ qs, q.dst = r.src ∧ q.index = r.index ∧ q.entries = r.ents

theorem RespMsg.mono {id T T' : w64} {qs qs' : List ReadReq} {q : Msg} (h : RespMsg id T qs q)
    (hT : T = T') (hs : ∀ r ∈ qs, r ∈ qs') : RespMsg id T' qs' q := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, r, hr, h8⟩ := h
  exact ⟨h1, h2, hT ▸ h3, h4, h5, h6, h7, r, hs r hr, h8⟩

/-- **Answering read requests** (`preadRespondAll`) queues their `MsgReadIndexResp`s. -/
theorem preadRespondAll_out (id : w64) (s : PState) (qs : List ReadReq) :
    ∃ ms, PKeep s (preadRespondAll id s qs) ∧ (preadRespondAll id s qs).outbox = s.outbox ++ ms ∧
      ∀ q ∈ ms, RespMsg id s.term qs q := by
  induction qs generalizing s with
  | nil => exact ⟨[], rfl, by simp [preadRespondAll_nil], fun q hq => by cases hq⟩
  | cons r qs ih =>
    rw [preadRespondAll_cons]
    have h1 : ∃ m1, PKeep s (preadRespond id s r) ∧ (preadRespond id s r).outbox = s.outbox ++ m1 ∧
        ∀ q ∈ m1, RespMsg id s.term [r] q := by
      unfold preadRespond
      split
      · split
        · exact ⟨[], rfl, by simp, fun q hq => by cases hq⟩
        · exact ⟨[], rfl, by simp, fun q hq => by cases hq⟩
      · rename_i hne
        refine ⟨_, rfl, rfl, fun q hq => ?_⟩
        rw [List.mem_singleton.mp hq]
        exact ⟨rfl, rfl, rfl, fun h => hne (.inr h), fun h => hne (.inl h), rfl, rfl, r,
          List.mem_singleton_self _, rfl, rfl, rfl⟩
    obtain ⟨m1, hk1, ho1, hm1⟩ := h1
    obtain ⟨m2, hk2, ho2, hm2⟩ := ih (preadRespond id s r)
    refine ⟨m1 ++ m2, hk1.trans hk2, by rw [ho2, ho1, List.append_assoc], fun q hq => ?_⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact (hm1 q hq).mono rfl fun x hx => by
        rw [List.mem_singleton.mp hx]; exact List.mem_cons_self ..
    · exact (hm2 q hq).mono (hk1.term) fun x hx => List.mem_cons_of_mem _ hx

/-- **The deferred reads' release** (`ReleaseEnd`) at `X`: heartbeats a leader sends at `X`, or
the answers of the released requests (read at the commit index). -/
theorem releaseEnd_out {c : CfgM} {id : w64} {X s2 : PState} (h : ReleaseEnd c id X s2) :
    ∃ ms, PKeep X s2 ∧ s2.outbox = X.outbox ++ ms ∧ ∀ q ∈ ms,
      HbSendOk c id X q ∨
      RespMsg id X.term (X.rd.pend.map (fun p => (⟨X.commit, p.1.From', p.2⟩ : ReadReq))) q := by
  rcases h with ⟨-, hb, hhb, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨hb, rfl, rfl, fun q hq => .inl (hhb q hq).1⟩
  · obtain ⟨ms, hk, ho, hms⟩ := preadRespondAll_out id { X with rd := { X.rd with pend := [] } }
      (X.rd.pend.map (fun p => (⟨X.commit, p.1.From', p.2⟩ : ReadReq)))
    exact ⟨ms, (pkeep_rd _ _).trans hk, ho, fun q hq => .inr (hms q hq)⟩

theorem releaseEnd_keep {c : CfgM} {id : w64} {X s2 : PState} (h : ReleaseEnd c id X s2) :
    PKeep X s2 :=
  (releaseEnd_out h).elim fun _ h => h.1

theorem readonlyRecvAck_pending (r : ReadOnly) (src : w64) (ctx : List w8) :
    (readonlyRecvAck r src ctx).pending = r.pending := by
  unfold readonlyRecvAck; split <;> rfl

theorem readonlyAdvance_sub (r : ReadOnly) (N : w64) : ∀ x ∈ (readonlyAdvance r N).2, x ∈ r.pending := by
  intro x hx
  unfold readonlyAdvance at hx
  split at hx
  · cases hx
  · exact List.mem_of_mem_take hx

/-- **A read acknowledgement** (`ReadAckEnd`) at `s`: the answers of requests of the leader's
read-only queue. -/
theorem readAckEnd_out {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadAckEnd c id s m s') :
    ∃ ms qs, PKeep s s' ∧ s'.outbox = s.outbox ++ ms ∧ (∀ r ∈ qs, r ∈ s.rd.ro.pending) ∧
      ∀ q ∈ ms, RespMsg id s.term qs q := by
  rcases h with ⟨-, rfl⟩ | ⟨N, -, rfl⟩
  · exact ⟨[], [], rfl, by simp, by simp, by simp⟩
  · obtain ⟨ms, hk, ho, hms⟩ := preadRespondAll_out id
      { s with rd := { s.rd with ro := (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).1 } }
      (readonlyAdvance (readonlyRecvAck s.rd.ro m.src m.ctx) N).2
    refine ⟨ms, _, (pkeep_rd _ _).trans hk, ho, fun r hr => ?_, hms⟩
    have := readonlyAdvance_sub _ N r hr
    rwa [readonlyRecvAck_pending] at this

theorem readAckEnd_keep {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadAckEnd c id s m s') :
    PKeep s s' :=
  (readAckEnd_out h).elim fun _ h => h.elim fun _ h => h.1

/-- **`MsgReadIndex`** (`ReadIdxEnd`) at `s`: a leader's heartbeats, the request's answer, or a
follower's forward to its leader. -/
theorem readIdxEnd_out {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadIdxEnd c id s m s') :
    ∃ ms, PKeep s s' ∧ s'.outbox = s.outbox ++ ms ∧ ∀ q ∈ ms,
      (s.role = .leader ∧ HbSendOk c id s q) ∨ RespMsg id s.term [⟨s.commit, m.src, m.entries⟩] q ∨
      (s.role = .follower ∧ s.lead ≠ W64 0 ∧
        q = Msg.mkV .readIndex (if m.src = W64 0 then id else m.src) s.lead (W64 0)
          m.reject m.index m.logterm m.commit m.rejecthint m.entries [] m.ctx) := by
  unfold ReadIdxEnd at h
  split at h
  · rename_i hr
    rcases h with ⟨-, pm, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, ms, hms, rfl⟩
    · exact ⟨[], rfl, by simp, fun q hq => by cases hq⟩
    · obtain ⟨ms, hk, ho, hms⟩ := preadRespondAll_out id s [⟨s.commit, m.src, m.entries⟩]
      exact ⟨ms, hk, ho, fun q hq => .inr (.inl (hms q hq))⟩
    · exact ⟨ms, rfl, rfl, fun q hq => .inl ⟨hr, (hms q hq).1⟩⟩
  · split at h
    · rename_i hf
      subst h
      exact ⟨_, rfl, rfl, fun q hq => .inr (.inr ⟨hf.1, hf.2, List.mem_singleton.mp hq⟩)⟩
    · subst h; exact ⟨[], rfl, by simp, fun q hq => by cases hq⟩

theorem readIdxEnd_keep {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadIdxEnd c id s m s') :
    PKeep s s' :=
  (readIdxEnd_out h).elim fun _ h => h.1

/-- `MsgApp`s judged at a leader's state `X` (`SendsEnd`'s, the broadcast after a win or a
proposal). -/
theorem outOk_apps {id : w64} {w : NodeView} {X : PState} {ms : List Msg} (hX : X.outbox = [])
    (hr : X.role = .leader) (hms : ∀ x ∈ ms, x.dst ≠ id → AppSendOk cf id X x) :
    OutOk N id w (psendMsgs X ms) := by
  intro q hq hne hd
  exact pendOk_app (w := w.withP _) hne hd hr (hms q (mem_psend hX hq) hne).1

theorem outOk_sends {id : w64} {w : NodeView} {X s' : PState} (hX : X.outbox = [])
    (hr : X.role = .leader) (h : SendsEnd cf id X s') : OutOk N id w s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact outOk_apps hX hr fun x hx _ => hms x hx

/-- `SendsEnd` after messages already `OutOk` (a release's, a read acknowledgement's). -/
theorem outOk_sends' {id : w64} {w : NodeView} {X s' : PState} (hX : OutOk N id w X)
    (hr : X.role = .leader) (h : SendsEnd cf id X s') : OutOk N id w s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact hX.keep (pkeep_psend _ _) rfl fun q hq hne hd =>
    pendOk_app (w := w.withP _) hne hd hr (hms q hq).1

theorem pendOk_hbSend {id : w64} {w : NodeView} {s : PState} {x : Msg} (hr : s.role = .leader)
    (h : HbSendOk cf id s x) (hne : x.dst ≠ id) (hd : ∃ j : Fin N, x.dst = nodeId j) :
    PendOk N id (w.withP s) x :=
  pendOk_heartbeat (w := w.withP s) hne hd hr h.1 h.2.1 h.2.2.1 h.2.2.2.1

theorem pendOk_resp {id T : w64} {w : NodeView} {t : PState} {qs : List ReadReq} {q : Msg}
    (ht : t.term = T) (h : RespMsg id T qs q) (hne : q.dst ≠ id) (hd : ∃ j : Fin N, q.dst = nodeId j) :
    PendOk N id (w.withP t) q := by
  unfold PendOk; rw [h.1]; exact ⟨hne, hd, h.2.1, h.2.2.1.trans ht.symm⟩

theorem outOk_respondAll {id : w64} {w : NodeView} {s : PState} {qs : List ReadReq}
    (h : OutOk N id w s) : OutOk N id w (preadRespondAll id s qs) := by
  obtain ⟨ms, hk, ho, hms⟩ := preadRespondAll_out id s qs
  exact h.keep hk ho fun q hq hne hd => pendOk_resp (hk.term) (hms q hq) hne hd

theorem outOk_release {id : w64} {w : NodeView} {X s2 : PState} (hX : OutOk N id w X)
    (hr : X.role = .leader) (h : ReleaseEnd cf id X s2) : OutOk N id w s2 := by
  obtain ⟨ms, hk, ho, hms⟩ := releaseEnd_out h
  refine hX.keep hk ho fun q hq hne hd => ?_
  rcases hms q hq with hh | hh
  · exact hk.pendOk (pendOk_hbSend hr hh hne hd)
  · exact pendOk_resp (hk.term) hh hne hd

theorem outOk_readAck {id : w64} {w : NodeView} {s s' : PState} {m : Msg} (hX : OutOk N id w s)
    (h : ReadAckEnd cf id s m s') : OutOk N id w s' := by
  obtain ⟨ms, qs, hk, ho, -, hms⟩ := readAckEnd_out h
  exact hX.keep hk ho fun q hq hne hd => pendOk_resp (hk.term) (hms q hq) hne hd

/-- A read request's messages (`ReadIdxEnd`, from a state with nothing queued): a leader's
heartbeats, the answer, a forward from the request's source (a node, or the node itself for a local
request). -/
theorem outOk_readIdx {id : w64} {w : NodeView} {s s' : PState} {m : Msg} (hX : s.outbox = [])
    (hid : ∃ j : Fin N, id = nodeId j) (hsrc : m.src = W64 0 ∨ ∃ j : Fin N, m.src = nodeId j)
    (h : ReadIdxEnd cf id s m s') : OutOk N id w s' := by
  obtain ⟨ms, hk, ho, hms⟩ := readIdxEnd_out h
  refine (outOk_nil hX).keep hk ho fun q hq hne hd => ?_
  rcases hms q hq with ⟨hr, hh⟩ | hh | ⟨-, -, rfl⟩
  · exact hk.pendOk (pendOk_hbSend hr hh hne hd)
  · exact pendOk_resp (hk.term) hh hne hd
  · refine ⟨hne, hd, ?_⟩
    show W64 0 = W64 0 ∧ ∃ j : Fin N, (if m.src = W64 0 then id else m.src) = nodeId j
    refine ⟨rfl, ?_⟩
    split
    · obtain ⟨j, hj⟩ := hid; exact ⟨j, hj⟩
    · rename_i h0; exact hsrc.resolve_left h0

theorem pselfAck_dst (id : w64) (s : PState) : (pselfAck id s).dst = id := rfl

theorem outOk_win {id : w64} {w : NodeView} {X s' : PState} (hX : X.outbox = [])
    (h : WinEnd cf id X s') : OutOk N id w s' := by
  obtain ⟨mt, ms, -, hms, rfl⟩ := h
  refine outOk_apps (cf := cf) hX rfl fun x hx hne => ?_
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
  · exact hms x hx

theorem outOk_propose {id : w64} {w : NodeView} {X s' : PState} {m : Msg} (hX : X.outbox = [])
    (h : ProposeEnd cf id X m s') : OutOk N id w s' := by
  unfold ProposeEnd at h
  split at h
  · rename_i hr
    rcases h with rfl | ⟨es, ms, -, hms, rfl⟩
    · exact outOk_nil hX
    · refine outOk_apps (cf := cf) hX hr fun x hx hne => ?_
      rcases List.mem_append.mp hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
      · exact hms x hx
  · split at h
    · subst h
      intro q hq hne hd
      rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
      exact pendOk_propose hne hd rfl rfl rfl
    · subst h; exact outOk_nil hX

/-- What the preamble keeps (`PreEndO`): the outbox, base, log and commit; its term is the message's. -/
theorem preEnd_facts {s s1 : PState} {m : Msg} (h : PreEndO kk s m s1) :
    s1.outbox = s.outbox ∧ s1.base = s.base ∧ s1.log = s.log ∧ s1.commit = s.commit ∧
      s1.term = m.term := by
  rcases h with ⟨-, rfl⟩ | ⟨ht, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, ht.symm⟩

/-- `handleAppendEntries`'s answer (`AppEnd`) at `X` (the state after the preamble, the sender
adopted): an acknowledgement of the handled `MsgApp` at the node's term, accepting at the batch's
last index with the log matching it, or stale at the commit index. -/
theorem outOk_appEnd {id : w64} {w : NodeView} {X s' : PState} {m : Msg} (hX : X.outbox = [])
    (hb : X.base = base0) (ht : X.term = m.term) (hby : w.byE = go!"recv")
    (hca : w.cause = some m) (hty : m.ty = .app) (hpay : AppPayloadOk m)
    (h : AppEnd id X m s') : OutOk N id w s' := by
  have hrecv : ∀ (q : Msg) (s'' : PState), q.ty = .appResp → q.src = id → q.dst = m.src →
      q.term = m.term → s''.term = m.term →
      (q.reject = false →
        (uint.Z q.index = uint.Z m.index + m.entries.length ∧
          plogTermAt s''.base s''.log m.index = some m.logterm ∧
          ∀ (k : Nat) (e : EntryM), m.entries[k]? = some e →
            plogTermAt s''.base s''.log (m.index + W64 ((k : Int) + 1)) = some e.Term') ∨
        (uint.Z m.index < uint.Z s''.commit ∧ q.index = s''.commit)) →
      q.dst ≠ id → (∃ j : Fin N, q.dst = nodeId j) → PendOk N id (w.withP s'') q := by
    intro q s'' hqt hqs hqd hqtm hst hacc hne hd
    unfold PendOk; rw [hqt]
    exact ⟨hne, hd, hqs, hby, .inl ⟨m, hca, hty, hqd, hqtm, hqtm.trans hst.symm, hacc⟩⟩
  rcases h with ⟨hlt, rfl⟩ | ⟨hle, lastnewi, es', hma, rfl⟩ | ⟨hle, -, hint, hintterm, -, -, rfl⟩
  · intro q hq hne hd
    rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
    exact hrecv _ _ rfl rfl rfl ht ht (fun _ => .inr ⟨hlt, rfl⟩) hne hd
  · intro q hq hne hd
    rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
    refine hrecv _ _ rfl rfl rfl ht ht (fun _ => .inl ?_) hne hd
    rw [hb] at hma
    obtain ⟨hwf, hnw⟩ := hpay
    obtain ⟨-, hli, -⟩ := plogMaybeAppend_inv _ _ _ _ _ _ hwf hnw hma
    have hbat := plogMaybeAppend_batch _ _ _ _ _ _ hwf hnw hma
    simp only at hli hbat hnw
    refine ⟨hli, ?_, fun k e hk => ?_⟩
    · show plogTermAt X.base es' m.index = some m.logterm
      rw [hb, hbat m.index (Int.le_refl _) (by have := uint_Z_nonneg m.index; omega)]
      exact plogTermAt_base _ _
    · show plogTermAt X.base es' (m.index + W64 ((k : Int) + 1)) = some e.Term'
      rw [hb]
      have hk' := (List.getElem?_eq_some_iff.mp hk).1
      have hj : uint.Z (m.index + W64 ((k : Int) + 1)) = uint.Z m.index + (k : Int) + 1 := by
        have := uint_Z_nonneg m.index
        have h1 : uint.Z (W64 ((k : Int) + 1)) = (k : Int) + 1 := uint_Z_W64 _ (by omega) (by omega)
        have h2 : uint.Z m.index + ((k : Int) + 1) < 2 ^ 64 := by omega
        word
      rw [hbat _ (by omega) (by omega)]
      exact plogTermAt_lookup _ _ _ k e hk (by simp only; push_cast; omega)
  · intro q hq hne hd
    rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
    exact hrecv _ _ rfl rfl rfl ht ht (fun h => absurd h (by simp)) hne hd

/-- The S4 network's types (`InMask.s4`'s order) in the order of the per-type lemmas. -/
theorem ty7_of_s4 {t : MsgType}
    (h : t = .app ∨ t = .appResp ∨ t = .vote ∨ t = .voteResp ∨ t = .heartbeat ∨ t = .heartbeatResp ∨
      t = .propose) :
    t = .vote ∨ t = .voteResp ∨ t = .app ∨ t = .appResp ∨ t = .heartbeat ∨ t = .heartbeatResp ∨
      t = .propose := by
  rcases h with h | h | h | h | h | h | h <;> simp [h]

/-- The type switch's messages (`HandleEndO`) at the state after the preamble, for a message of a
type the readings read (a read request's source a node or local). -/
theorem outOk_handle {c : CfgM} {id : w64} {w : NodeView} {s1 s' : PState} {m : Msg}
    (hX : s1.outbox = []) (hb : s1.base = base0) (ht : s1.term = m.term)
    (hby : w.byE = go!"recv") (hca : w.cause = some m) (hpay : m.ty = .app → AppPayloadOk m)
    (hid : ∃ j : Fin N, id = nodeId j) (hsrc : m.src = W64 0 ∨ ∃ j : Fin N, m.src = nodeId j)
    (hsc : RdTy m.ty) (h : HandleEndO kk c id s1 m s') : OutOk N id w s' := by
  unfold HandleEndO at h
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at h; simp only at h; exact outOk_readIdx hX hid hsrc h
  · rw [hty] at h; simp only at h
    split at h
    · rcases h with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact outOk_nil hX
    · subst h; exact outOk_nil hX
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · intro q hq hne hd
      rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
      exact pendOk_voteResp hne hd rfl rfl ht.symm fun _ => rfl
    · intro q hq hne hd
      rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
      exact pendOk_voteResp hne hd rfl rfl rfl fun h => absurd h (by simp [Msg.plain])
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact outOk_nil hX
      · exact outOk_win hX hw
      · exact outOk_nil hX
    · subst h; exact outOk_nil hX
  · split at h
    · subst h; exact outOk_nil hX
    · exact outOk_appEnd (X := padoptLeader s1 m.src) hX hb ht hby hca hty (hpay hty) h
  · split at h
    · rename_i hr
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩ | ⟨-, x, n, s2, -, -, hrel, hs⟩
      · exact outOk_nil hX
      · exact outOk_sends hX hr hs
      · exact outOk_sends (X := { s1 with matched := _, commit := n }) hX hr hs
      · exact outOk_sends' (outOk_release (X := { s1 with matched := _, commit := n }) (outOk_nil hX)
          hr hrel) (((releaseEnd_keep hrel).role).trans hr) hs
    · subst h; exact outOk_nil hX
  · split at h
    · subst h; exact outOk_nil hX
    · subst h
      intro q hq hne hd
      rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
      exact pendOk_heartbeatResp hne hd rfl rfl rfl
  · split at h
    · rename_i hr
      obtain ⟨s2, hs, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact outOk_sends hX hr hs
      · exact outOk_readAck (outOk_sends hX hr hs) ha
    · subst h; exact outOk_nil hX
  · exact outOk_propose hX h

/-- A received message's step (`RecvEndO`), its term not `0` but a forwarded read request's
(`RawNode.Step`'s `NetMsgOk`; `send` stamps no term on a `MsgReadIndex`). -/
theorem outOk_recv {c : CfgM} {id : w64} {w : NodeView} {s s' : PState} {m : Msg}
    (hX : s.outbox = []) (hb : s.base = base0) (hm0 : m.ty ≠ .readIndex → m.term ≠ W64 0)
    (hby : w.byE = go!"recv") (hca : w.cause = some m) (hpay : m.ty = .app → AppPayloadOk m)
    (hsc : RdTy m.ty) (hid : ∃ j : Fin N, id = nodeId j)
    (hsrc : m.src = W64 0 ∨ ∃ j : Fin N, m.src = nodeId j)
    (h : RecvEndO kk c id s m s') : OutOk N id w s' := by
  rcases h with ⟨h0, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · have hty : m.ty = .readIndex := Classical.byContradiction fun hne => hm0 hne h0
    unfold HandleEndO at hh; rw [hty] at hh; simp only at hh
    exact outOk_readIdx hX hid hsrc hh
  · exact outOk_nil hX
  · obtain ⟨ho, hb1, -, -, ht⟩ := preEnd_facts hpre
    exact outOk_handle (ho.trans hX) (hb1.trans hb) ht hby hca hpay hid hsrc hsc hh

/-- A tick's messages (`TickEndO`): a campaign's vote requests, a leader's heartbeats. -/
theorem outOk_tick {c : CfgM} {id : w64} {w : NodeView} {s s' : PState}
    (hX : s.outbox = []) (hb : s.base = base0) (h : TickEndO kk c id s s') : OutOk N id w s' := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨hr, ms, hms, rfl⟩
  · exact outOk_nil hX
  · intro q hq hne hd
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
      exact pendOk_vote (w := w.withP _) hne hd rfl rfl rfl rfl rfl rfl rfl
  · intro q hq hne hd
    obtain ⟨hh, hi, hlt, he, -⟩ := hms q (mem_psend hX hq)
    exact pendOk_heartbeat (w := w.withP _) hne hd hr hh hi hlt he

/-! ## The pre-vote and check-quorum arms' messages (below `mskB1`) -/

theorem pendOk_preVote {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin N, q.dst = nodeId j) (hty : q.ty = .preVote) (hs : q.src = id)
    (hv : id ∈ w.r.cfg.cfg.voters) : PendOk N id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, hv⟩

theorem pendOk_preVoteResp {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin N, q.dst = nodeId j) (hty : q.ty = .preVoteResp) (hs : q.src = id)
    (hg : q.reject = false → ∃ m, w.cause = some m ∧ m.ty = .preVote ∧ q.dst = m.src)
    (hrj : q.reject = true → q.term = w.ps.term) : PendOk N id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, hg, hrj⟩

/-- A campaign's messages (`CampaignSends`, from a state with nothing queued): its vote requests. -/
theorem outOk_campaignSends {c : CfgM} {id : w64} {w : NodeView} {X s' : PState} {cl : List w8}
    (hX : X.outbox = []) (h : CampaignSends c id X cl s') : OutOk N id w s' := by
  obtain ⟨peers, -, rfl⟩ := h
  intro q hq hne hd
  rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
  · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
  · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
    exact pendOk_vote (w := w.withP _) hne hd rfl rfl rfl rfl rfl rfl rfl

/-- A received message's new arm (`RecvEndP`): the stale `MsgApp`/`MsgHeartbeat`'s empty answer,
a pre-vote request's answer (a grant to the handled request's sender), a campaign's requests. -/
theorem outOk_recvP {c : CfgM} {id : w64} {w : NodeView} {s s' : PState} {m : Msg}
    (hX : s.outbox = []) (hby : w.byE = go!"recv") (hca : w.cause = some m)
    (h : RecvEndP kk c id s m s') : OutOk N id w s' := by
  rcases h with ⟨hlt, -, hty, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨hty, hpv⟩ | ⟨-, -, -, rfl⟩ |
      ⟨-, rfl | ⟨-, -, -, hcs⟩⟩
  · intro q hq hne hd
    rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
    unfold PendOk
    exact ⟨hne, hd, rfl, hby, .inr ⟨m, hca, hty, rfl, hlt, rfl⟩⟩
  · intro q hq hne hd
    rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
    exact pendOk_preVoteResp hne hd rfl rfl (fun h => absurd h (by simp [Msg.plain])) fun _ => rfl
  · exact outOk_nil hX
  · rcases hpv with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · intro q hq hne hd
      rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
      exact pendOk_preVoteResp hne hd rfl rfl (fun _ => ⟨m, hca, hty, rfl⟩)
        fun h => absurd h (by simp [Msg.plain])
    · intro q hq hne hd
      rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
      exact pendOk_preVoteResp hne hd rfl rfl (fun h => absurd h (by simp [Msg.plain])) fun _ => rfl
  · exact outOk_nil (s := pbecomeFollower s _ _) hX
  · exact outOk_nil hX
  · exact outOk_campaignSends hX hcs

/-- A tick's new arm (`TickEndP`): a pre-campaign's pre-vote requests (a voter's, at the view's
configuration), nothing at a check-quorum step-down. -/
theorem outOk_tickP {c : CfgM} {id : w64} {w : NodeView} {s s' : PState}
    (hX : s.outbox = []) (hc : c = w.r.cfg.cfg) (h : TickEndP kk c id s s') : OutOk N id w s' := by
  rcases h with ⟨-, -, hid, peers, -, rfl⟩ | ⟨-, -, rfl⟩
  · intro q hq hne hd
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
      exact pendOk_preVote (w := w.withP _) hne hd rfl rfl (hc ▸ hid)
  · exact outOk_nil (s := pbecomeFollower s _ _) hX

/-! ## `Advance`'s messages -/

/-- A self-addressed message `Advance` steps at the term `T` (`QsOk`'s shape). -/
def SelfMsg (id T : w64) (q : Msg) : Prop :=
  q.src = id ∧ q.dst = id ∧ q.term = T ∧ q.reject = false ∧ (q.ty = .appResp ∨ q.ty = .voteResp)

/-- A message `Advance`'s steps queue to another node at `s`: a leader's `MsgApp`, `AppOk` at `s`
with a commit at least `c₀`; with reads, a heartbeat (`HeartbeatOk` at `s`, a deferred read's
release) or a read request's answer at `s`'s term (`ReleaseEnd`). -/
def AdvOut (id c₀ : w64) (s : PState) (q : Msg) : Prop :=
  (AppOk id s q ∧ uint.Z c₀ ≤ uint.Z q.commit) ∨
  (HeartbeatOk id s q ∧ q.index = W64 0 ∧ q.logterm = W64 0 ∧ q.entries = []) ∨
  (q.ty = .readIndexResp ∧ q.src = id ∧ q.term = s.term)

/-- What `Advance`'s steps keep, from a state of term `T` and commit `c₀` with nothing queued:
the term; the commit at least `c₀`; anything queued is a leader's, to another node `AdvOut`, its
self-addressed ones its self-acknowledgement. -/
def AdvInv (id T c₀ : w64) (s : PState) : Prop :=
  s.term = T ∧ uint.Z c₀ ≤ uint.Z s.commit ∧
  ∀ q ∈ s.outbox, s.role = .leader ∧ (q.dst ≠ id → AdvOut id c₀ s q) ∧
    (q.dst = id → q = pselfAck id s)

theorem AppOk.mono {id : w64} {s s' : PState} {q : Msg} (ht : s'.term = s.term)
    (hb : s'.base = s.base) (hl : s'.log = s.log) (hc : uint.Z s.commit ≤ uint.Z s'.commit)
    (h : AppOk id s q) : AppOk id s' q := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, ht ▸ h3, h4, hb ▸ hl ▸ h5, by omega, hl ▸ h7, hb ▸ hl ▸ h8, h9⟩

theorem HeartbeatOk.mono {id : w64} {s s' : PState} {q : Msg} (ht : s'.term = s.term)
    (hc : uint.Z s.commit ≤ uint.Z s'.commit)
    (hm : ∀ d, uint.Z (matchOf s d) ≤ uint.Z (matchOf s' d)) (h : HeartbeatOk id s q) :
    HeartbeatOk id s' q := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3.trans ht.symm, h4, by omega, by have := hm q.dst; omega⟩

theorem AdvOut.mono {id c₀ : w64} {s s' : PState} {q : Msg} (ht : s'.term = s.term)
    (hb : s'.base = s.base) (hl : s'.log = s.log) (hc : uint.Z s.commit ≤ uint.Z s'.commit)
    (hm : ∀ d, uint.Z (matchOf s d) ≤ uint.Z (matchOf s' d)) (h : AdvOut id c₀ s q) :
    AdvOut id c₀ s' q := by
  rcases h with ⟨ha, hc'⟩ | ⟨hh, h2⟩ | ⟨h1, h2, h3⟩
  · exact .inl ⟨AppOk.mono ht hb hl hc ha, hc'⟩
  · exact .inr (.inl ⟨HeartbeatOk.mono ht hc hm hh, h2⟩)
  · exact .inr (.inr ⟨h1, h2, h3.trans ht.symm⟩)

/-- An acknowledgement raises the sender's `Match` (`max`). -/
theorem matchOf_raise {s : PState} {src x idx : w64} (hx : s.matched !! src = some x) (d : w64) :
    uint.Z (matchOf s d) ≤ uint.Z (matchOf { s with matched :=
      <[src := (if uint.Z x < uint.Z idx then idx else x)]> s.matched } d) := by
  show uint.Z ((s.matched !! d).getD (W64 0)) ≤
    uint.Z (((<[src := (if uint.Z x < uint.Z idx then idx else x)]> s.matched) !! d).getD (W64 0))
  by_cases hd : src = d
  · subst hd; rw [hx, lookup_insert]; simp only [Option.getD_some]; split <;> omega
  · rw [lookup_insert_ne _ _ hd]; exact Int.le_refl _

theorem advInv_nil {id T c₀ : w64} {s : PState} (ht : s.term = T) (hc : uint.Z c₀ ≤ uint.Z s.commit)
    (hX : s.outbox = []) : AdvInv id T c₀ s :=
  ⟨ht, hc, fun q hq => by rw [hX] at hq; cases hq⟩

theorem AdvInv.nil_of {id T c₀ : w64} {s : PState} (hi : AdvInv id T c₀ s) (hr : s.role ≠ .leader) :
    s.outbox = [] := by
  cases ho : s.outbox with
  | nil => rfl
  | cons q _ => exact absurd (hi.2.2 q (by rw [ho]; exact List.mem_cons_self ..)).1 hr

/-- An acknowledgement's `Match` and commit raise at a leader. -/
theorem advInv_commit {id T c₀ : w64} {s : PState} {src x idx n : w64} (hi : AdvInv id T c₀ s)
    (hx : s.matched !! src = some x) (hcn : uint.Z s.commit ≤ uint.Z n) :
    AdvInv id T c₀ { s with
      matched := (<[src := (if uint.Z x < uint.Z idx then idx else x)]> s.matched), commit := n } := by
  obtain ⟨ht, hc, hall⟩ := hi
  refine ⟨ht, show uint.Z c₀ ≤ uint.Z n by omega, fun y hy => ?_⟩
  obtain ⟨hr', hok, hself⟩ := hall y hy
  exact ⟨hr', fun hne => AdvOut.mono (s := s) rfl rfl rfl hcn (matchOf_raise (idx := idx) hx) (hok hne),
    fun he => hself he⟩

/-- Messages queued at `t`, `s` but for its outbox and read state. -/
theorem advInv_keep {id T c₀ : w64} {s t : PState} {ms : List Msg} (hi : AdvInv id T c₀ s)
    (hr : s.role = .leader) (hk : PKeep s t) (ho : t.outbox = s.outbox ++ ms)
    (hms : ∀ q ∈ ms, q.dst ≠ id ∧ AdvOut id c₀ t q) : AdvInv id T c₀ t := by
  have ht : t.term = s.term := hk.term
  have hb : t.base = s.base := hk.base
  have hl : t.log = s.log := hk.log
  have hc : t.commit = s.commit := hk.commit
  have hm : t.matched = s.matched := hk.matched
  have hro : t.role = s.role := hk.role
  obtain ⟨hT, hc0, hall⟩ := hi
  refine ⟨ht.trans hT, hc ▸ hc0, fun q hq => ?_⟩
  rw [ho] at hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨-, hok, hself⟩ := hall q hq
    refine ⟨hro.trans hr, fun hne => AdvOut.mono ht hb hl (by rw [hc]; exact Int.le_refl _)
      (fun d => by unfold matchOf; rw [hm]; exact Int.le_refl _) (hok hne), fun he => ?_⟩
    rw [hself he]; unfold pselfAck plastIndex; rw [ht, hb, hl]
  · exact ⟨hro.trans hr, fun _ => (hms q hq).2, fun he => absurd he (hms q hq).1⟩

/-- A leader's appends (`SendsEnd`) keep `AdvInv`: at the commit index, at least `c₀`. -/
theorem advInv_sends {id T c₀ : w64} {s s' : PState} (hi : AdvInv id T c₀ s)
    (hr : s.role = .leader) (h : SendsEnd cf id s s') : AdvInv id T c₀ s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  refine advInv_keep hi hr (pkeep_psend _ _) rfl fun y hy => ?_
  have hy' := hms y hy
  refine ⟨hy'.1.2.2.2.1, .inl ⟨hy'.1, ?_⟩⟩
  rw [hy'.2.1 hy'.1.1]; exact hi.2.1

/-- The deferred reads' release keeps `AdvInv`: its heartbeats and answers at the leader's term. -/
theorem advInv_release {id T c₀ : w64} {X s2 : PState} (hi : AdvInv id T c₀ X)
    (hr : X.role = .leader) (h : ReleaseEnd cf id X s2) : AdvInv id T c₀ s2 := by
  obtain ⟨ms, hk, ho, hms⟩ := releaseEnd_out h
  have ht : s2.term = X.term := hk.term
  have hc : s2.commit = X.commit := hk.commit
  have hm : s2.matched = X.matched := hk.matched
  refine advInv_keep hi hr hk ho fun q hq => ?_
  rcases hms q hq with hh | hh
  · refine ⟨hh.1.2.2.2.1, .inr (.inl ⟨HeartbeatOk.mono ht (by rw [hc]; exact Int.le_refl _)
      (fun d => by unfold matchOf; rw [hm]; exact Int.le_refl _) hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩)⟩
  · exact ⟨hh.2.2.2.1, .inr (.inr ⟨hh.1, hh.2.1, hh.2.2.1.trans ht.symm⟩)⟩

/-- One step of `Advance` (the type switch at the state itself: the message is at its term). -/
theorem adv_handle {c : CfgM} {id T c₀ : w64} {s s1 : PState} {q : Msg} (hi : AdvInv id T c₀ s)
    (hq : SelfMsg id T q) (h : HandleEndO kk c id s q s1) :
    AdvInv id T c₀ s1 := by
  obtain ⟨-, -, -, hrj, hty⟩ := hq
  unfold HandleEndO at h
  rcases hty with hty | hty <;> rw [hty] at h <;> simp only at h
  · split at h
    · rename_i hr
      rcases h with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨-, x, n, hx, hn, hs⟩ | ⟨-, x, n, s2, hx, hn, hrel, hs⟩
      · exact hi
      · rw [hrj] at h'; cases h'
      · have hcn : uint.Z s.commit ≤ uint.Z n := by
          rcases hn with rfl | hn
          · exact Int.le_refl _
          · exact Int.le_of_lt hn.1
        exact advInv_sends (advInv_commit (idx := q.index) hi hx hcn) hr hs
      · have h1 := advInv_commit (idx := q.index) hi hx (Int.le_of_lt hn.1)
        exact advInv_sends (advInv_release h1 hr hrel)
          (((releaseEnd_keep hrel).role).trans hr) hs
    · subst h; exact hi
  · split at h
    · rename_i hr
      have hX := hi.nil_of (by rw [hr]; decide)
      obtain ⟨ht, hc, -⟩ := hi
      rcases h with ⟨-, rfl⟩ | ⟨-, mt, ms, -, hms, rfl⟩ | ⟨-, rfl⟩
      · exact advInv_nil ht hc hX
      · refine ⟨ht, hc, fun y hy => ?_⟩
        rcases List.mem_append.mp (mem_psend hX hy) with hy | hy
        · rw [List.mem_singleton.mp hy]
          exact ⟨rfl, fun hne => absurd rfl hne, fun _ => rfl⟩
        · have hy' := hms y hy
          refine ⟨rfl, fun _ => .inl ⟨hy'.1, ?_⟩, fun he => absurd he hy'.1.2.2.2.1⟩
          rw [hy'.2.1 hy'.1.1]; exact hc
      · exact advInv_nil ht hc hX
    · subst h; exact hi

/-- One step of `Advance` (`RecvEndO` of a self-addressed message at the node's term). -/
theorem adv_step {c : CfgM} {id T c₀ : w64} {s s1 : PState} {q : Msg} (hi : AdvInv id T c₀ s)
    (hq : SelfMsg id T q) (h : RecvEndO kk c id s q s1) :
    AdvInv id T c₀ s1 := by
  have hqt : q.term = s.term := hq.2.2.1.trans hi.1.symm
  rcases h with ⟨-, hh⟩ | ⟨-, hlt, -⟩ | ⟨-, s2, hpre, hh⟩
  · exact adv_handle hi hq hh
  · rw [hqt] at hlt; exact absurd hlt (Int.lt_irrefl _)
  · rcases hpre with ⟨hlt, -⟩ | ⟨-, rfl⟩
    · rw [hqt] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · exact adv_handle hi hq hh

theorem adv_run {c : CfgM} {id T c₀ : w64} {s s' : PState} {qs : List Msg}
    (h : AdvanceEndO kk c id s qs s') (hq : ∀ q ∈ qs, SelfMsg id T q) (hi : AdvInv id T c₀ s) :
    AdvInv id T c₀ s' := by
  induction h with
  | nil => exact hi
  | cons s s1 s' q qs hr _ ih =>
    exact ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))
      (adv_step hi (hq q (List.mem_cons_self ..)) hr)

/-- `Advance`'s messages (`AdvanceEndO` of self-addressed messages from a state with nothing
queued): a leader's `MsgApp`s, `AppOk` at the end. -/
theorem outOk_advance {c : CfgM} {id : w64} {w : NodeView} {s s' : PState} {qs : List Msg}
    (hX : s.outbox = []) (hq : ∀ q ∈ qs, SelfMsg id s.term q) (h : AdvanceEndO kk c id s qs s') :
    OutOk N id w s' := by
  have hinv : AdvInv id s.term s.commit s' := adv_run h hq (advInv_nil rfl (Int.le_refl _) hX)
  intro x hx hne hd
  obtain ⟨hr, hok, -⟩ := hinv.2.2 x hx
  rcases hok hne with ⟨ha, -⟩ | ⟨hh, hi, hlt, he⟩ | ⟨hty, hs, ht⟩
  · exact pendOk_app (w := w.withP _) hne hd hr ha
  · exact pendOk_heartbeat (w := w.withP _) hne hd hr hh hi hlt he
  · unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, ht⟩

/-! ## The `Ready`'s messages -/

/-- **`OutOk` along `ReachP`**: one input's messages at its end state (C1: nothing queued before
it), `Advance`'s a leader's `MsgApp`s, heartbeats and read answers (`outOk_advance`) or a
pre-candidate's campaign. A received message is from a node (a forwarded read request's source). -/
theorem outOk_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView} {ps₁ : PState}
    (hX : v.ps.outbox = []) (hb : v.ps.base = base0) (hc : c = v.r.cfg.cfg)
    (hpay : ∀ m ∈ net, m.ty = .app → AppPayloadOk m)
    (hid : ∃ j : Fin N, id = nodeId j) (hsn : ∀ m ∈ net, ∃ j : Fin N, m.src = nodeId j)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → SelfMsg id v.ps.term q)
    (hr : ReachP kk c id net xnet v ps₁) : OutOk N id v ps₁ := by
  cases hr with
  | stay _ => exact outOk_nil hX
  | recv m _ _ hbe hca hmn _ hm0 hty h =>
    exact outOk_recv hX hb hm0 hbe hca (hpay m hmn) hty hid (.inr (hsn m hmn)) h
  | recvP m _ _ hbe hca _ _ _ _ h => exact outOk_recvP hX hbe hca h
  | tick _ _ _ h => exact outOk_tick hX hb h
  | tickP _ _ _ h => exact outOk_tickP hX hc h
  | propose d _ _ _ h => exact outOk_propose hX h
  | read d _ _ _ h => exact outOk_readIdx hX hid (.inl rfl) h
  | advance _ _ _ _ hno h => exact outOk_advance hX (fun q hq => hqs q hq (hno q hq)) h
  | advP _ _ _ _ _ _ _ h =>
    rcases h with rfl | ⟨-, -, hcs⟩
    · exact outOk_nil hX
    · exact outOk_campaignSends hX hcs
  | sends _ _ _ hl h => exact outOk_sends hX hl h
  | adoptX x _ _ _ _ _ _ => exact outOk_nil (show (pbecomeFollower v.ps _ _).outbox = [] from hX)
  | campX x p1 _ _ _ _ _ _ _ hp1 h =>
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact outOk_campaignSends (show (pbecomeFollower v.ps _ _).outbox = [] from hX) h.sends
    · exact outOk_campaignSends hX h.sends

/-- **Every message to another voter in the outbox of the state a `Ready` is taken at is
`PendOk`** at the view moved there (`outOk_reachP`). A received `MsgApp`'s batch is `AppPayloadOk`
(C4's `NetShape`: its sender's `AppOk`); a received message is from a server (`NetOk`); the queued
messages not pre-votes are `QsOk`'s self-acknowledgements and self-votes. For the runs a mask below
`mskB1` admits. -/
theorem outOk_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) : OutOk R.N (nodeId n) v r₁.p := by
  obtain ⟨hmd, -⟩ := hin.b1 hmsk
  refine outOk_reachP hv.facts.outbox (hv.facts.snap0 (by rw [hmd])).1 rfl
    (fun m hmn => (hnet.2.2.1 m hmn).1) ⟨n, rfl⟩
    (fun m hmn => by obtain ⟨i, hi, -⟩ := (hnet.1 m hmn).2.1; exact ⟨i, hi⟩) (fun q hq hne => ?_)
    (ReachIn.toP hmsk hin hnet hv hr)
  obtain ⟨h1, h2, h3, h4, h5⟩ := (hv.qs q hq).notPre hne
  exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩

/-! ## The leader hint along `Reach` -/

/-- Raft's leader hint at `s` (C1's `LeadOk`): a node that does not lead does not name itself; the
hint is no node or one of the three (`LeadIn`). -/
def LeadHint (N : Nat) (id : w64) (s : PState) : Prop := (s.role ≠ .leader → s.lead ≠ id) ∧ LeadIn N s

theorem leadHint_pre {id : w64} {s s1 : PState} {m : Msg} (h : LeadHint N id s) (hid : id ≠ W64 0)
    (hsrc : fromLeader m.ty = true → m.src ≠ id)
    (hsn : fromLeader m.ty = true → ∃ j : Fin N, m.src = nodeId j) (hp : PreEndO kk s m s1) :
    LeadHint N id s1 := by
  rcases hp with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨fun _ => ?_, ?_⟩
    · show (if fromLeader m.ty then m.src else W64 0) ≠ id
      split
      · rename_i hfl; exact hsrc hfl
      · exact Ne.symm hid
    · show (if fromLeader m.ty then m.src else W64 0) = W64 0 ∨
        ∃ j : Fin N, (if fromLeader m.ty then m.src else W64 0) = nodeId j
      split
      · rename_i hfl; exact .inr (hsn hfl)
      · exact .inl rfl
  · exact h

theorem leadHint_propose {id : w64} {s s' : PState} {m : Msg} (h : LeadHint N id s)
    (hp : ProposeEnd cf id s m s') : LeadHint N id s' := by
  unfold ProposeEnd at hp
  split at hp
  · rename_i hr
    rcases hp with rfl | ⟨es, ms, -, -, rfl⟩
    · exact h
    · exact ⟨fun h' => absurd hr h', h.2⟩
  · split at hp
    · subst hp; exact h
    · subst hp; exact h

theorem LeadHint.of_eq {id : w64} {s t : PState} (h : LeadHint N id s) (hr : t.role = s.role)
    (hl : t.lead = s.lead) : LeadHint N id t := by
  unfold LeadHint LeadIn at *; rw [hr, hl]; exact h

theorem LeadHint.keep {id : w64} {s t : PState} (h : LeadHint N id s) (hk : PKeep s t) :
    LeadHint N id t :=
  h.of_eq (hk.role) (hk.lead)

/-- The type switch keeps the leader hint: the sender adopted as leader (`MsgApp`, `MsgHeartbeat`)
is another node; a lost election clears `lead`; a win makes the node leader; the read arms change
only the outbox and the read state. -/
theorem leadHint_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : LeadHint N id s)
    (hid : id ≠ W64 0) (hin : ∃ j : Fin N, id = nodeId j) (hsc : RdTy m.ty)
    (hsrc : m.src ≠ id ∨ m.ty = .appResp ∨ m.ty = .voteResp ∨ m.ty = .readIndex)
    (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hh : HandleEndO kk c id s m s') : LeadHint N id s' := by
  unfold HandleEndO at hh
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at hh; simp only at hh; exact h.keep (readIdxEnd_keep hh)
  · rw [hty] at hh; simp only at hh
    split at hh
    · rcases hh with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h
    · subst hh; exact h
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at hh <;>
    simp only at hh
  · rcases hh with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact h
      · exact ⟨fun h' => absurd rfl h', .inr hin⟩
      · exact ⟨fun _ => Ne.symm hid, .inl rfl⟩
    · subst hh; exact h
  · have hs : m.src ≠ id := hsrc.resolve_right (by rw [hty]; simp)
    split at hh
    · subst hh; exact h
    · rcases hh with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, _, _, -, -, rfl⟩ <;>
        exact ⟨fun _ => hs, .inr hsn⟩
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨-, x, k, -, -, ms, -, rfl⟩ |
        ⟨-, x, k, s2, -, -, hrel, ms, -, rfl⟩
      · exact h
      · exact h
      · exact h
      · exact (h.of_eq ((releaseEnd_keep hrel).role)
          ((releaseEnd_keep hrel).lead)).keep (pkeep_psend _ _)
    · subst hh; exact h
  · have hs : m.src ≠ id := hsrc.resolve_right (by rw [hty]; simp)
    split at hh
    · subst hh; exact h
    · subst hh; exact ⟨fun _ => hs, .inr hsn⟩
  · split at hh
    · obtain ⟨s2, ⟨ms, -, rfl⟩, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := hh
      · exact h
      · exact (h.keep (pkeep_psend _ ms)).keep (readAckEnd_keep ha)
    · subst hh; exact h
  · exact leadHint_propose h hh

theorem leadHint_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : LeadHint N id s)
    (hid : id ≠ W64 0) (hin : ∃ j : Fin N, id = nodeId j) (hsc : RdTy m.ty)
    (hsrc : m.src ≠ id ∨ m.ty = .appResp ∨ m.ty = .voteResp ∨ m.ty = .readIndex)
    (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hr : RecvEndO kk c id s m s') : LeadHint N id s' := by
  rcases hr with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact leadHint_handle h hid hin hsc hsrc hsn hh
  · exact h
  · refine leadHint_handle (leadHint_pre h hid (fun hfl => ?_) (fun _ => hsn) hpre) hid hin hsc
      hsrc hsn hh
    rcases hsrc with hs | hty | hty | hty
    · exact hs
    all_goals exact absurd hfl (by simp [hty, fromLeader])

theorem leadHint_tick {c : CfgM} {id : w64} {s s' : PState} (h : LeadHint N id s) (hid : id ≠ W64 0)
    (ht : TickEndO kk c id s s') : LeadHint N id s' := by
  rcases ht with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
  · exact h
  · exact ⟨fun _ => Ne.symm hid, .inl rfl⟩
  · exact h

theorem leadHint_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg} (h : LeadHint N id s)
    (hid : id ≠ W64 0) (hin : ∃ j : Fin N, id = nodeId j)
    (hq : ∀ q ∈ qs, (q.ty = .appResp ∨ q.ty = .voteResp) ∧ q.src = id)
    (ha : AdvanceEndO kk c id s qs s') : LeadHint N id s' := by
  induction ha with
  | nil => exact h
  | cons s s1 s' q qs hr _ ih =>
    have hq0 := hq q (List.mem_cons_self ..)
    have hsc : RdTy q.ty := by
      rcases hq0.1 with h0 | h0 <;> simp [RdTy, S4Ty, h0]
    exact ih (leadHint_recv h hid hin hsc (.inr (hq0.1.imp (fun h => h) .inl)) (hq0.2 ▸ hin) hr)
      (fun x hx => hq x (List.mem_cons_of_mem _ hx))

/-- A campaign keeps the leader hint (a candidate with no leader). -/
theorem leadHint_campaignSends {c : CfgM} {id : w64} {s s' : PState} {cl : List w8}
    (hid : id ≠ W64 0) (h : CampaignSends c id s cl s') : LeadHint N id s' := by
  obtain ⟨peers, -, rfl⟩ := h
  exact ⟨fun _ => Ne.symm hid, .inl rfl⟩

/-- `RecvEndP` keeps the leader hint: the answers keep the state, a step-down or a campaign clears
`lead`. -/
theorem leadHint_recvP {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : LeadHint N id s)
    (hid : id ≠ W64 0) (hr : RecvEndP kk c id s m s') : LeadHint N id s' := by
  rcases hr with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ |
      ⟨-, -, -, rfl⟩ | ⟨-, rfl | ⟨-, -, -, hcs⟩⟩
  · exact h
  · exact h
  · exact h
  · exact h
  · exact h
  · exact ⟨fun _ => Ne.symm hid, .inl rfl⟩
  · exact h
  · exact leadHint_campaignSends hid hcs

/-- `TickEndP` keeps the leader hint: a pre-campaign and a step-down clear `lead`. -/
theorem leadHint_tickP {c : CfgM} {id : w64} {s s' : PState} (hid : id ≠ W64 0)
    (ht : TickEndP kk c id s s') : LeadHint N id s' := by
  rcases ht with ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact ⟨fun _ => Ne.symm hid, .inl rfl⟩
  · exact ⟨fun _ => Ne.symm hid, .inl rfl⟩

/-- **The leader hint along `ReachP`**: a received message is from another node, one of the
servers; `Advance` steps the node's own acknowledgements and vote responses, or a pre-candidate's
self pre-votes (nothing or the campaign). -/
theorem leadHint_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView} {ps₁ : PState}
    (h : LeadHint N id v.ps) (hid : id ≠ W64 0) (hin : ∃ j : Fin N, id = nodeId j)
    (hsd : ∀ m ∈ net, m.ty ≠ .readIndex → m.src ≠ m.dst)
    (hsn : ∀ m ∈ net, ∃ j : Fin N, m.src = nodeId j)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → (q.ty = .appResp ∨ q.ty = .voteResp) ∧ q.src = id)
    (hr : ReachP kk c id net xnet v ps₁) : LeadHint N id ps₁ := by
  cases hr with
  | stay _ => exact h
  | recv m _ _ _ _ hmn hmd _ hty hO =>
    refine leadHint_recv h hid hin hty ?_ (hsn m hmn) hO
    by_cases hri : m.ty = .readIndex
    · exact .inr (.inr (.inr hri))
    · exact .inl (hmd ▸ hsd m hmn hri)
  | recvP m _ _ _ _ _ _ _ _ hP => exact leadHint_recvP h hid hP
  | tick _ _ _ ht => exact leadHint_tick h hid ht
  | tickP _ _ _ ht => exact leadHint_tickP hid ht
  | propose d _ _ _ hh => exact leadHint_propose h hh
  | read d _ _ _ hh => exact h.keep (readIdxEnd_keep hh)
  | advance _ _ _ _ hno ha => exact leadHint_adv h hid hin (fun q hq => hqs q hq (hno q hq)) ha
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, hcs⟩
    · exact h
    · exact leadHint_campaignSends hid hcs
  | sends _ _ _ _ hs => obtain ⟨ms, -, rfl⟩ := hs; exact h.keep (pkeep_psend _ _)
  | adoptX x _ _ _ _ _ _ => exact ⟨fun _ => Ne.symm hid, .inl rfl⟩
  | campX x p1 _ _ _ _ _ _ _ _ hc => exact leadHint_campaignSends hid hc.sends

/-- **The leader hint is kept along `Reach`** (C1's `LeadOk` at the state a `Ready` is taken at,
`leadHint_reachP`): a received message is from another node (C4's `NetShape`) but a forwarded read
request, one of the servers (`NetOk`). For the runs a mask below `mskB1` admits. -/
theorem reach_leadOk {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) : LeadHint R.N (nodeId n) r₁.p := by
  refine leadHint_reachP hv.leadOk (nodeId_ne_zero n) ⟨n, rfl⟩ (fun m hmn => (hnet.2.2.1 m hmn).2.1)
    (fun m hmn => by obtain ⟨i, hi, -⟩ := (hnet.1 m hmn).2.1; exact ⟨i, hi⟩) (fun q hq hne => ?_)
    (ReachIn.toP hmsk hin hnet hv hr)
  obtain ⟨h1, -, -, -, h5⟩ := (hv.qs q hq).notPre hne
  exact ⟨h5.imp (fun h => h.1) (fun h => h.1), h1⟩

/-! ## What the pre-vote and check-quorum arms keep -/

/-- A queued self-message's type (`QsOk`): a self-acknowledgement, a self-vote or a self pre-vote. -/
theorem QsOk.ty3 {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (h : QsOk R S n v q) : q.ty = .appResp ∨ q.ty = .voteResp ∨ q.ty = .preVoteResp := by
  obtain ⟨-, -, -, ⟨-, h5 | h5⟩ | ⟨h6, -⟩⟩ := h
  · exact .inl h5.1
  · exact .inr (.inl h5.1)
  · exact .inr (.inr h6)

/-- A queued message other than a self pre-vote is `SelfMsg` at the view's term (`QsOk.notPre`). -/
theorem QsOk.self {R : RunCfg} {S : AntCheck.State} {n : Fin R.N} {v : NodeView} {q : Msg}
    (h : QsOk R S n v q) (hne : q.ty ≠ .preVoteResp) : SelfMsg (nodeId n) v.ps.term q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.notPre hne
  exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩

/-- A campaign keeps the log, the base and the commit index. -/
theorem campaignSends_keep {c : CfgM} {id : w64} {s s' : PState} {cl : List w8}
    (h : CampaignSends c id s cl s') : s'.log = s.log ∧ s'.base = s.base ∧ s'.commit = s.commit := by
  obtain ⟨peers, -, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩

/-- `RecvEndP` keeps the log, the base and the commit index. -/
theorem recvEndP_keep {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : RecvEndP kk c id s m s') :
    s'.log = s.log ∧ s'.base = s.base ∧ s'.commit = s.commit := by
  rcases h with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ |
      ⟨-, -, -, rfl⟩ | ⟨-, rfl | ⟨-, -, -, hcs⟩⟩
  all_goals first | exact ⟨rfl, rfl, rfl⟩ | exact campaignSends_keep hcs

/-- `TickEndP` keeps the log, the base and the commit index. -/
theorem tickEndP_keep {c : CfgM} {id : w64} {s s' : PState} (h : TickEndP kk c id s s') :
    s'.log = s.log ∧ s'.base = s.base ∧ s'.commit = s.commit := by
  rcases h with ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

/-! ## The read requests' sources along `Reach` (`NodeFacts.readSrc`) -/

/-- Every read request's source, deferred (`rd.pend`) or in a leader's read-only queue, is local
(`0`) or a node, and its entries normal when `cc = false` (`NodeFacts.readSrc`'s body at a protocol
state, at `cc = R.md.confChanges`). -/
def ReadSrc (N : Nat) (cc : Bool) (s : PState) : Prop :=
  (∀ p ∈ s.rd.pend, (p.1.From' = W64 0 ∨ ∃ j : Fin N, p.1.From' = nodeId j) ∧
    (cc = false → EntsNormal p.2)) ∧
  (s.role = .leader → ∀ q ∈ s.rd.ro.pending, (q.src = W64 0 ∨ ∃ j : Fin N, q.src = nodeId j) ∧
    (cc = false → EntsNormal q.ents))

/-- The local read request's entry (its context) is normal. -/
theorem readMsg_normal (d : List w8) : EntsNormal (readMsg d).entries := by
  intro e he; simp only [readMsg, List.mem_singleton] at he; subst he; rfl

theorem ReadSrc.of {s t : PState} (h : ReadSrc N cc s) (hp : t.rd.pend = s.rd.pend)
    (hro : t.role = .leader → s.role = .leader ∧ ∀ q ∈ t.rd.ro.pending, q ∈ s.rd.ro.pending) :
    ReadSrc N cc t :=
  ⟨fun p hp' => h.1 p (hp ▸ hp'), fun hr q hq => h.2 (hro hr).1 q ((hro hr).2 q hq)⟩

theorem ReadSrc.nl {s t : PState} (h : ReadSrc N cc s) (hp : t.rd.pend = s.rd.pend)
    (hr : t.role ≠ .leader) : ReadSrc N cc t :=
  h.of hp fun h' => absurd h' hr

theorem ReadSrc.ro0 {s t : PState} (h : ReadSrc N cc s) (hp : t.rd.pend = s.rd.pend)
    (hro : t.rd.ro.pending = []) : ReadSrc N cc t :=
  ⟨fun p hp' => h.1 p (hp ▸ hp'), fun _ q hq => by rw [hro] at hq; cases hq⟩

theorem preadRespondAll_rd (id : w64) (s : PState) (qs : List ReadReq) :
    (preadRespondAll id s qs).rd.pend = s.rd.pend ∧ (preadRespondAll id s qs).rd.ro = s.rd.ro := by
  induction qs generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons r qs ih =>
    rw [preadRespondAll_cons]
    obtain ⟨h1, h2⟩ := ih (preadRespond id s r)
    rw [h1, h2]
    unfold preadRespond
    split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

theorem readSrc_respondAll {id : w64} {s : PState} {qs : List ReadReq} (h : ReadSrc N cc s) :
    ReadSrc N cc (preadRespondAll id s qs) := by
  obtain ⟨-, hk, -⟩ := preadRespondAll_out id s qs
  have hrd := preadRespondAll_rd id s qs
  exact h.of hrd.1 fun hr => ⟨hk.role.symm.trans hr, fun q hq => by rw [hrd.2] at hq; exact hq⟩

theorem readonlyArrive_pending (r : ReadOnly) (id : w64) (q : ReadReq) :
    (readonlyArrive r id q).pending = r.pending ++ [q] := by
  unfold readonlyArrive; rw [readonlyRecvAck_pending]; rfl

theorem readonlyRelease_pending (r : ReadOnly) (id c : w64) (pend : List (MessageM × List EntryM)) :
    (readonlyRelease r id c pend).pending =
      r.pending ++ pend.map (fun p => (⟨c, p.1.From', p.2⟩ : ReadReq)) := by
  induction pend generalizing r with
  | nil => simp [readonlyRelease]
  | cons p ps ih =>
    unfold readonlyRelease at *
    rw [List.foldl_cons, ih, readonlyArrive_pending]; simp

theorem readonlyAdvance_pending (r : ReadOnly) (N : w64) :
    ∀ q ∈ (readonlyAdvance r N).1.pending, q ∈ r.pending := by
  intro q hq
  unfold readonlyAdvance at hq
  split at hq
  · exact hq
  · exact List.mem_of_mem_drop hq

/-- A read request's step keeps `ReadSrc`, the request's source local or a node. -/
theorem readSrc_readIdx {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadSrc N cc s)
    (hsrc : (m.src = W64 0 ∨ ∃ j : Fin N, m.src = nodeId j) ∧ (cc = false → EntsNormal m.entries))
    (hR : ReadIdxEnd c id s m s') :
    ReadSrc N cc s' := by
  unfold ReadIdxEnd at hR
  split at hR
  · rcases hR with ⟨-, pm, hpm, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, ms, -, rfl⟩
    · refine ⟨fun p hp => ?_, h.2⟩
      rcases List.mem_append.mp hp with hp | hp
      · exact h.1 p hp
      · rw [List.mem_singleton.mp hp]
        exact ⟨by show pm.From' = W64 0 ∨ _; rw [hpm]; exact hsrc.1, hsrc.2⟩
    · exact readSrc_respondAll h
    · refine ⟨h.1, fun hr q hq => ?_⟩
      change q ∈ (readonlyArrive s.rd.ro id _).pending at hq
      rw [readonlyArrive_pending] at hq
      rcases List.mem_append.mp hq with hq | hq
      · exact h.2 hr q hq
      · rw [List.mem_singleton.mp hq]; exact hsrc
  · split at hR
    · subst hR; exact h
    · subst hR; exact h

/-- The deferred reads' release keeps `ReadSrc` at a leader: the released requests' sources are the
deferred ones'. -/
theorem readSrc_release {c : CfgM} {id : w64} {X s2 : PState} (h : ReadSrc N cc X)
    (hr : X.role = .leader) (hR : ReleaseEnd c id X s2) : ReadSrc N cc s2 := by
  rcases hR with ⟨-, hb, -, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨fun p hp => (by cases hp), fun _ q hq => ?_⟩
    change q ∈ (readonlyRelease X.rd.ro id X.commit X.rd.pend).pending at hq
    rw [readonlyRelease_pending] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h.2 hr q hq
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq; exact h.1 p hp
  · exact readSrc_respondAll (s := { X with rd := { X.rd with pend := [] } })
      ⟨fun p hp => (by cases hp), h.2⟩

theorem readSrc_readAck {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadSrc N cc s)
    (hR : ReadAckEnd c id s m s') : ReadSrc N cc s' := by
  rcases hR with ⟨-, rfl⟩ | ⟨N', -, rfl⟩
  · refine h.of rfl fun hr => ⟨hr, fun q hq => ?_⟩
    change q ∈ (readonlyRecvAck s.rd.ro m.src m.ctx).pending at hq
    rwa [readonlyRecvAck_pending] at hq
  · refine readSrc_respondAll (h.of rfl fun hr => ⟨hr, fun q hq => ?_⟩)
    have := readonlyAdvance_pending _ N' q hq
    rwa [readonlyRecvAck_pending] at this

theorem readSrc_sends {c : CfgM} {id : w64} {X s' : PState} (h : ReadSrc N cc X) (hs : SendsEnd c id X s') :
    ReadSrc N cc s' := by
  obtain ⟨ms, -, rfl⟩ := hs; exact h

/-- The type switch keeps `ReadSrc`: every arm keeps the read state and the role, makes the node a
follower or leader (`pbecomeLeader` resets the queue), or is a read arm. -/
theorem readSrc_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadSrc N cc s)
    (hsc : RdTy m.ty)
    (hsrc : m.ty = .readIndex → (m.src = W64 0 ∨ ∃ j : Fin N, m.src = nodeId j) ∧
      (cc = false → EntsNormal m.entries))
    (hh : HandleEndO kk c id s m s') : ReadSrc N cc s' := by
  unfold HandleEndO at hh
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at hh; simp only at hh; exact readSrc_readIdx h (hsrc hty) hh
  · rw [hty] at hh; simp only at hh
    split at hh
    · rcases hh with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h
    · subst hh; exact h
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at hh <;>
    simp only at hh
  · rcases hh with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact h
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact h
      · obtain ⟨mt, ms, -, -, rfl⟩ := hw; exact h.ro0 rfl rfl
      · exact h.nl rfl (by simp [pbecomeFollower])
    · subst hh; exact h
  · split at hh
    · subst hh; exact h
    · rcases hh with ⟨-, rfl⟩ | ⟨-, lastnewi, es', -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩ <;>
        exact h.nl rfl (by simp [psendMsgs, padoptLeader])
  · split at hh
    · rename_i hr
      rcases hh with ⟨-, rfl⟩ | ⟨-, -, hs'⟩ | ⟨-, x, n, -, -, hs'⟩ | ⟨-, x, n, s2, -, -, hrel, hs'⟩
      · exact h
      · exact readSrc_sends h hs'
      · exact readSrc_sends (X := { s with matched := _, commit := n }) h hs'
      · exact readSrc_sends (readSrc_release (X := { s with matched := _, commit := n }) h hr hrel) hs'
    · subst hh; exact h
  · split at hh
    · subst hh; exact h
    · subst hh; exact h.nl rfl (by simp [psendMsgs, padoptLeader])
  · split at hh
    · obtain ⟨s2, hs', ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := hh
      · exact readSrc_sends h hs'
      · exact readSrc_readAck (readSrc_sends h hs') ha
    · subst hh; exact h
  · unfold ProposeEnd at hh
    split at hh
    · rcases hh with rfl | ⟨es, ms, -, -, rfl⟩ <;> exact h
    · split at hh
      · subst hh; exact h
      · subst hh; exact h

theorem readSrc_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : ReadSrc N cc s)
    (hsc : RdTy m.ty)
    (hsrc : m.ty = .readIndex → (m.src = W64 0 ∨ ∃ j : Fin N, m.src = nodeId j) ∧
      (cc = false → EntsNormal m.entries))
    (hr : RecvEndO kk c id s m s') : ReadSrc N cc s' := by
  rcases hr with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact readSrc_handle h hsc hsrc hh
  · exact h
  · refine readSrc_handle ?_ hsc hsrc hh
    rcases hpre with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact h.nl rfl (by simp [pbecomeFollower])
    · exact h

theorem readSrc_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg} (h : ReadSrc N cc s)
    (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp) (ha : AdvanceEndO kk c id s qs s') :
    ReadSrc N cc s' := by
  induction ha with
  | nil => exact h
  | cons s s1 s' q qs hr _ ih =>
    have hty := hq q (List.mem_cons_self ..)
    refine ih ?_ (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    refine readSrc_recv h ?_ (fun h' => by rcases hty with h'' | h'' <;> rw [h''] at h' <;> cases h') hr
    rcases hty with h' | h' <;> simp [RdTy, S4Ty, h']

/-- **`ReadSrc` along `ReachP`**: a request enters only by `ReadIdxEnd`, from a received message
(whose sender is a node, `NetOk`) or the local `readMsg` (source `0`); the release and the
acknowledgement move requests between the deferred list and the queue, or answer them; a new role
resets the queue. -/
theorem readSrc_reachP {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView} {ps₁ : PState}
    (h : ReadSrc N cc v.ps) (hsn : ∀ m ∈ net, ∃ j : Fin N, m.src = nodeId j)
    (hen : ∀ m ∈ net, cc = false → EntsNormal m.entries)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → q.ty = .appResp ∨ q.ty = .voteResp)
    (hr : ReachP kk c id net xnet v ps₁) : ReadSrc N cc ps₁ := by
  cases hr with
  | stay _ => exact h
  | recv m _ _ _ _ hmn _ _ hty hO => exact readSrc_recv h hty (fun _ => ⟨.inr (hsn m hmn), hen m hmn⟩) hO
  | recvP m _ _ _ _ _ _ _ _ hP =>
    rcases hP with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ |
        ⟨-, -, -, rfl⟩ | ⟨-, rfl | ⟨-, -, -, hcs⟩⟩
    · exact h
    · exact h
    · exact h
    · exact h
    · exact h
    · exact h.nl rfl (by simp [pbecomeFollower])
    · exact h
    · obtain ⟨peers, -, rfl⟩ := hcs; exact h.nl rfl (by simp [psendMsgs, pbecomeCandidate])
  | tick _ _ _ ht =>
    rcases ht with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
    · exact h
    · exact h.nl rfl (by simp [psendMsgs, pbecomeCandidate])
    · exact h
  | tickP _ _ _ ht =>
    rcases ht with ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact h.nl rfl (by simp [psendMsgs])
    · exact h.nl rfl (by simp [pbecomeFollower])
  | propose d _ _ _ hh =>
    unfold ProposeEnd at hh
    split at hh
    · rcases hh with rfl | ⟨es, ms, -, -, rfl⟩ <;> exact h
    · split at hh
      · subst hh; exact h
      · subst hh; exact h
  | read d _ _ _ hh => exact readSrc_readIdx h ⟨.inl rfl, fun _ => readMsg_normal d⟩ hh
  | advance _ _ _ _ hno ha => exact readSrc_adv h (fun q hq => hqs q hq (hno q hq)) ha
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, hcs⟩
    · exact h
    · obtain ⟨peers, -, rfl⟩ := hcs; exact h.nl rfl (by simp [psendMsgs, pbecomeCandidate])
  | sends _ _ _ _ hs => exact readSrc_sends h hs
  | adoptX x _ _ _ _ _ _ => exact h.nl rfl (by simp [pbecomeFollower])
  | campX x p1 _ _ _ _ _ _ _ hp1 hc =>
    obtain ⟨-, peers, -, rfl⟩ := hc
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact h.nl rfl (by simp [psendMsgs, pbecomeCandidate])

/-- **The read requests' sources along `Reach`** (`NodeFacts.readSrc` at the state a `Ready` is
taken at, `readSrc_reachP`): the view's (`NodeFacts.readSrc`), a received message's sender a server
(`NetOk`). For the runs a mask below `mskB1` admits. -/
theorem readSrc_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    ReadSrc R.N R.md.confChanges r₁.p :=
  readSrc_reachP hv.facts.readSrc
    (fun m hmn => by obtain ⟨i, hi, -⟩ := (hnet.1 m hmn).2.1; exact ⟨i, hi⟩)
    (fun m hmn => (hnet.2.2.2.2.1 m hmn).1)
    (fun q hq hne => ((hv.qs q hq).self hne).2.2.2.2) (ReachIn.toP hmsk hin hnet hv hr)

end outbox

end AntSim
end EtcdGrove
end Perennial
