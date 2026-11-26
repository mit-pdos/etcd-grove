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
variable {cf : CfgM} {N : Nat} {kk : NodeK}

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

/-- The type switch's messages (`HandleEndO`) at the state after the preamble, for a message of a
type the network carries. -/
theorem outOk_handle {c : CfgM} {id : w64} {w : NodeView} {s1 s' : PState} {m : Msg}
    (hX : s1.outbox = []) (hb : s1.base = base0) (ht : s1.term = m.term)
    (hby : w.byE = go!"recv") (hca : w.cause = some m) (hpay : m.ty = .app → AppPayloadOk m)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : HandleEndO kk c id s1 m s') : OutOk N id w s' := by
  unfold HandleEndO at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
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
      unfold AppRespEndO at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩
      · exact outOk_nil hX
      · exact outOk_sends hX hr hs
      · exact outOk_sends (X := { s1 with matched := _, commit := n }) hX hr hs
    · subst h; exact outOk_nil hX
  · split at h
    · subst h; exact outOk_nil hX
    · subst h
      intro q hq hne hd
      rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
      exact pendOk_heartbeatResp hne hd rfl rfl rfl
  · split at h
    · rename_i hr; exact outOk_sends hX hr h
    · subst h; exact outOk_nil hX
  · exact outOk_propose hX h

/-- A received message's step (`RecvEndO`), its term not `0` (`RawNode.Step`'s `NetMsgOk`). -/
theorem outOk_recv {c : CfgM} {id : w64} {w : NodeView} {s s' : PState} {m : Msg}
    (hX : s.outbox = []) (hb : s.base = base0) (hm0 : m.term ≠ W64 0)
    (hby : w.byE = go!"recv") (hca : w.cause = some m) (hpay : m.ty = .app → AppPayloadOk m)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : RecvEndO kk c id s m s') : OutOk N id w s' := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact outOk_nil hX
  · obtain ⟨ho, hb1, -, -, ht⟩ := preEnd_facts hpre
    exact outOk_handle (ho.trans hX) (hb1.trans hb) ht hby hca hpay hsc hh

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

/-! ## The pre-vote and check-quorum arms' messages (below `mskB1p`) -/

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

/-- What `Advance`'s steps keep, from a state of term `T` and commit `c₀` with nothing queued:
the term; the commit at least `c₀`; anything queued is a leader's, its `MsgApp`s `AppOk` at the
current state with a commit at least `c₀`, its self-addressed ones its self-acknowledgement. -/
def AdvInv (id T c₀ : w64) (s : PState) : Prop :=
  s.term = T ∧ uint.Z c₀ ≤ uint.Z s.commit ∧
  ∀ q ∈ s.outbox, s.role = .leader ∧ (q.dst ≠ id → AppOk id s q ∧ uint.Z c₀ ≤ uint.Z q.commit) ∧
    (q.dst = id → q = pselfAck id s)

theorem AppOk.mono {id : w64} {s s' : PState} {q : Msg} (ht : s'.term = s.term)
    (hb : s'.base = s.base) (hl : s'.log = s.log) (hc : uint.Z s.commit ≤ uint.Z s'.commit)
    (h : AppOk id s q) : AppOk id s' q := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, ht ▸ h3, h4, hb ▸ hl ▸ h5, by omega, hl ▸ h7, hb ▸ hl ▸ h8, h9⟩

theorem advInv_nil {id T c₀ : w64} {s : PState} (ht : s.term = T) (hc : uint.Z c₀ ≤ uint.Z s.commit)
    (hX : s.outbox = []) : AdvInv id T c₀ s :=
  ⟨ht, hc, fun q hq => by rw [hX] at hq; cases hq⟩

theorem AdvInv.nil_of {id T c₀ : w64} {s : PState} (hi : AdvInv id T c₀ s) (hr : s.role ≠ .leader) :
    s.outbox = [] := by
  cases ho : s.outbox with
  | nil => rfl
  | cons q _ => exact absurd (hi.2.2 q (by rw [ho]; exact List.mem_cons_self ..)).1 hr

/-- One step of `Advance` (the type switch at the state itself: the message is at its term). -/
theorem adv_handle {c : CfgM} {id T c₀ : w64} {s s1 : PState} {q : Msg} (hi : AdvInv id T c₀ s)
    (hq : SelfMsg id T q) (h : HandleEndO kk c id s q s1) :
    AdvInv id T c₀ s1 := by
  obtain ⟨-, -, -, hrj, hty⟩ := hq
  unfold HandleEndO at h
  rcases hty with hty | hty <;> rw [hty] at h <;> simp only at h
  · split at h
    · rename_i hr
      unfold AppRespEndO at h
      rcases h with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨-, x, n, -, hn, ms, hms, rfl⟩
      · exact hi
      · rw [hrj] at h'; cases h'
      · have hcn : uint.Z s.commit ≤ uint.Z n := by
          rcases hn with rfl | hn
          · exact Int.le_refl _
          · exact Int.le_of_lt hn.1
        obtain ⟨ht, hc, hall⟩ := hi
        refine ⟨ht, show uint.Z c₀ ≤ uint.Z n by omega, fun y hy => ?_⟩
        rw [psendMsgs_outbox] at hy
        rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨hr', hok, hself⟩ := hall y hy
          refine ⟨hr', fun hne => ?_, fun he => hself he⟩
          obtain ⟨hao, hyc⟩ := hok hne
          exact ⟨AppOk.mono (s := s) rfl rfl rfl hcn hao, hyc⟩
        · have hy' := hms y hy
          refine ⟨hr, fun _ => ⟨hy'.1, ?_⟩, fun he => absurd he hy'.1.2.2.2.1⟩
          rw [hy'.2.1 hy'.1.1]; show uint.Z c₀ ≤ uint.Z n; omega
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
          refine ⟨rfl, fun _ => ⟨hy'.1, ?_⟩, fun he => absurd he hy'.1.2.2.2.1⟩
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
  exact pendOk_app (w := w.withP _) hne hd hr (hok hne).1

/-! ## The `Ready`'s messages -/

/-- The S4 network's types (`InMask.s4`'s order) in the order of the per-type lemmas. -/
theorem ty7_of_s4 {t : MsgType}
    (h : t = .app ∨ t = .appResp ∨ t = .vote ∨ t = .voteResp ∨ t = .heartbeat ∨ t = .heartbeatResp ∨
      t = .propose) :
    t = .vote ∨ t = .voteResp ∨ t = .app ∨ t = .appResp ∨ t = .heartbeat ∨ t = .heartbeatResp ∨
      t = .propose := by
  rcases h with h | h | h | h | h | h | h <;> simp [h]

/-- **`OutOk` along `ReachP`**: one input's messages at its end state (C1: nothing queued before
it), `Advance`'s a leader's `MsgApp`s (`outOk_advance`) or a pre-candidate's campaign. -/
theorem outOk_reachP {c : CfgM} {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState}
    (hX : v.ps.outbox = []) (hb : v.ps.base = base0) (hc : c = v.r.cfg.cfg)
    (hpay : ∀ m ∈ net, m.ty = .app → AppPayloadOk m)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → SelfMsg id v.ps.term q)
    (hr : ReachP kk c id net v ps₁) : OutOk N id v ps₁ := by
  cases hr with
  | stay _ => exact outOk_nil hX
  | recv m _ _ hbe hca hmn _ hm0 hs4 h =>
    exact outOk_recv hX hb hm0 hbe hca (hpay m hmn) (ty7_of_s4 hs4) h
  | recvP m _ _ hbe hca _ _ _ _ h => exact outOk_recvP hX hbe hca h
  | tick _ _ _ h => exact outOk_tick hX hb h
  | tickP _ _ _ h => exact outOk_tickP hX hc h
  | propose d _ _ _ h => exact outOk_propose hX h
  | advance _ _ _ _ hno h => exact outOk_advance hX (fun q hq => hqs q hq (hno q hq)) h
  | advP _ _ _ _ _ _ _ h =>
    rcases h with rfl | ⟨-, -, hcs⟩
    · exact outOk_nil hX
    · exact outOk_campaignSends hX hcs

/-- **Every message to another voter in the outbox of the state a `Ready` is taken at is
`PendOk`** at the view moved there (`outOk_reachP`). A received `MsgApp`'s batch is `AppPayloadOk`
(C4's `NetShape`: its sender's `AppOk`); the queued messages not pre-votes are `QsOk`'s
self-acknowledgements and self-votes. For the runs a mask below `mskB1p` admits. -/
theorem outOk_reach {msk : SimMask} (hmsk : msk ≤ mskB1p) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) : OutOk R.N (nodeId n) v r₁.p := by
  obtain ⟨hmd, -⟩ := hin.b1p hmsk
  refine outOk_reachP hv.facts.outbox (hv.facts.snap0 (by rw [hmd])).1 rfl
    (fun m hmn => (hnet.2.2.1 m hmn).1) (fun q hq hne => ?_) (ReachIn.toP hmsk hin hnet hv hr)
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

/-- The type switch keeps the leader hint: the sender adopted as leader (`MsgApp`, `MsgHeartbeat`)
is another node; a lost election clears `lead`; a win makes the node leader. -/
theorem leadHint_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : LeadHint N id s)
    (hid : id ≠ W64 0) (hin : ∃ j : Fin N, id = nodeId j)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hsrc : m.src ≠ id ∨ m.ty = .appResp ∨ m.ty = .voteResp)
    (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hh : HandleEndO kk c id s m s') : LeadHint N id s' := by
  unfold HandleEndO at hh
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at hh <;> simp only at hh
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
    · unfold AppRespEndO at hh
      rcases hh with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨-, x, k, -, -, ms, -, rfl⟩ <;> exact h
    · subst hh; exact h
  · have hs : m.src ≠ id := hsrc.resolve_right (by rw [hty]; simp)
    split at hh
    · subst hh; exact h
    · subst hh; exact ⟨fun _ => hs, .inr hsn⟩
  · split at hh
    · obtain ⟨ms, -, rfl⟩ := hh; exact h
    · subst hh; exact h
  · exact leadHint_propose h hh

theorem leadHint_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (h : LeadHint N id s)
    (hid : id ≠ W64 0) (hin : ∃ j : Fin N, id = nodeId j)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hsrc : m.src ≠ id ∨ m.ty = .appResp ∨ m.ty = .voteResp)
    (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hr : RecvEndO kk c id s m s') : LeadHint N id s' := by
  rcases hr with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact leadHint_handle h hid hin hsc hsrc hsn hh
  · exact h
  · refine leadHint_handle (leadHint_pre h hid (fun hfl => ?_) (fun _ => hsn) hpre) hid hin hsc
      hsrc hsn hh
    rcases hsrc with hs | hty | hty
    · exact hs
    · exact absurd hfl (by simp [hty, fromLeader])
    · exact absurd hfl (by simp [hty, fromLeader])

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
    have hsc : q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨
        q.ty = .heartbeat ∨ q.ty = .heartbeatResp ∨ q.ty = .propose := by
      rcases hq0.1 with h0 | h0
      · exact .inr (.inr (.inr (.inl h0)))
      · exact .inr (.inl h0)
    exact ih (leadHint_recv h hid hin hsc (.inr hq0.1) (hq0.2 ▸ hin) hr)
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
theorem leadHint_reachP {c : CfgM} {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState}
    (h : LeadHint N id v.ps) (hid : id ≠ W64 0) (hin : ∃ j : Fin N, id = nodeId j)
    (hsd : ∀ m ∈ net, m.src ≠ m.dst) (hsn : ∀ m ∈ net, ∃ j : Fin N, m.src = nodeId j)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → (q.ty = .appResp ∨ q.ty = .voteResp) ∧ q.src = id)
    (hr : ReachP kk c id net v ps₁) : LeadHint N id ps₁ := by
  cases hr with
  | stay _ => exact h
  | recv m _ _ _ _ hmn hmd _ hs4 hO =>
    exact leadHint_recv h hid hin (ty7_of_s4 hs4) (.inl (hmd ▸ hsd m hmn)) (hsn m hmn) hO
  | recvP m _ _ _ _ _ _ _ _ hP => exact leadHint_recvP h hid hP
  | tick _ _ _ ht => exact leadHint_tick h hid ht
  | tickP _ _ _ ht => exact leadHint_tickP hid ht
  | propose d _ _ _ hh => exact leadHint_propose h hh
  | advance _ _ _ _ hno ha => exact leadHint_adv h hid hin (fun q hq => hqs q hq (hno q hq)) ha
  | advP _ _ _ _ _ _ _ ha =>
    rcases ha with rfl | ⟨-, -, hcs⟩
    · exact h
    · exact leadHint_campaignSends hid hcs

/-- **The leader hint is kept along `Reach`** (C1's `LeadOk` at the state a `Ready` is taken at,
`leadHint_reachP`): a received message is from another node (C4's `NetShape`), one of the servers
(`NetOk`). For the runs a mask below `mskB1p` admits. -/
theorem reach_leadOk {msk : SimMask} (hmsk : msk ≤ mskB1p) {R : RunCfg} {dec : CCDec}
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

end outbox

end AntSim
end EtcdGrove
end Perennial
