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

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Stmts

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap

section outbox
variable [GooseExts]

/-! ## `PendOk` per message type -/

/-- `PendOk` reads only the view's role, term, vote, log, base, commit, `Match`, `by` and cause. -/
theorem PendOk.congr {id : w64} {v w : NodeView} {q : Msg} (hr : w.ps.role = v.ps.role)
    (ht : w.ps.term = v.ps.term) (hv : w.ps.vote = v.ps.vote) (hl : w.ps.log = v.ps.log)
    (hb : w.ps.base = v.ps.base) (hc : w.ps.commit = v.ps.commit)
    (hm : w.ps.matched = v.ps.matched) (hbe : w.byE = v.byE) (hca : w.cause = v.cause)
    (h : PendOk id v q) : PendOk id w q := by
  unfold PendOk AppOk HeartbeatOk matchOf at *
  rw [hr, ht, hv, hl, hb, hc, hm, hbe, hca]; exact h

theorem pendOk_app {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin 3, q.dst = nodeId j) (hr : w.ps.role = .leader) (ha : AppOk id w.ps q) :
    PendOk id w q := by
  have hty : q.ty = .app := ha.1
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hr, ha⟩

theorem pendOk_vote {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin 3, q.dst = nodeId j) (hty : q.ty = .vote) (hs : q.src = id)
    (hr : w.ps.role = .candidate) (ht : q.term = w.ps.term) (hv : w.ps.vote = id)
    (hi : q.index = (plogLast base0 w.ps.log).index')
    (hlt : q.logterm = (plogLast base0 w.ps.log).term') : PendOk id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, hr, ht, hv, hi, hlt⟩

theorem pendOk_voteResp {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin 3, q.dst = nodeId j) (hty : q.ty = .voteResp) (hs : q.src = id)
    (ht : q.term = w.ps.term) (hv : q.reject = false → w.ps.vote = q.dst) : PendOk id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, ht, hv⟩

theorem pendOk_heartbeatResp {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin 3, q.dst = nodeId j) (hty : q.ty = .heartbeatResp) (hs : q.src = id)
    (ht : q.term = w.ps.term) : PendOk id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, ht⟩

theorem pendOk_propose {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin 3, q.dst = nodeId j) (hty : q.ty = .propose) (hs : q.src = id)
    (ht : q.term = W64 0) : PendOk id w q := by
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hs, ht⟩

theorem pendOk_heartbeat {id : w64} {w : NodeView} {q : Msg} (hne : q.dst ≠ id)
    (hd : ∃ j : Fin 3, q.dst = nodeId j) (hr : w.ps.role = .leader) (hh : HeartbeatOk id w.ps q)
    (hi : q.index = W64 0) (hlt : q.logterm = W64 0) (he : q.entries = []) : PendOk id w q := by
  have hty : q.ty = .heartbeat := hh.1
  unfold PendOk; rw [hty]; exact ⟨hne, hd, hr, hh, hi, hlt, he⟩

/-! ## One input's messages, judged at its end state -/

/-- Every message to another voter in `s`'s outbox is `PendOk` at the view `w` moved to `s`. -/
def OutOk (id : w64) (w : NodeView) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst ≠ id → (∃ j : Fin 3, q.dst = nodeId j) → PendOk id { w with ps := s } q

theorem outOk_nil {id : w64} {w : NodeView} {s : PState} (h : s.outbox = []) : OutOk id w s := by
  intro q hq; rw [h] at hq; cases hq

theorem mem_psend {X : PState} {ms : List Msg} {q : Msg} (hX : X.outbox = [])
    (hq : q ∈ (psendMsgs X ms).outbox) : q ∈ ms := by
  rw [psendMsgs_outbox, hX, List.nil_append] at hq; exact hq

/-- `MsgApp`s judged at a leader's state `X` (`SendsEnd`'s, the broadcast after a win or a
proposal). -/
theorem outOk_apps {id : w64} {w : NodeView} {X : PState} {ms : List Msg} (hX : X.outbox = [])
    (hr : X.role = .leader) (hms : ∀ x ∈ ms, x.dst ≠ id → AppSendOk id X x) :
    OutOk id w (psendMsgs X ms) := by
  intro q hq hne hd
  exact pendOk_app hne hd hr (hms q (mem_psend hX hq) hne).1

theorem outOk_sends {id : w64} {w : NodeView} {X s' : PState} (hX : X.outbox = [])
    (hr : X.role = .leader) (h : SendsEnd id X s') : OutOk id w s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact outOk_apps hX hr fun x hx _ => hms x hx

theorem pselfAck_dst (id : w64) (s : PState) : (pselfAck id s).dst = id := rfl

theorem outOk_win {id : w64} {w : NodeView} {X s' : PState} (hX : X.outbox = [])
    (h : WinEnd id X s') : OutOk id w s' := by
  obtain ⟨mt, ms, -, hms, rfl⟩ := h
  refine outOk_apps hX rfl fun x hx hne => ?_
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
  · exact hms x hx

theorem outOk_propose {id : w64} {w : NodeView} {X s' : PState} {m : Msg} (hX : X.outbox = [])
    (h : ProposeEnd id X m s') : OutOk id w s' := by
  unfold ProposeEnd at h
  split at h
  · rename_i hr
    rcases h with rfl | ⟨es, ms, -, hms, rfl⟩
    · exact outOk_nil hX
    · refine outOk_apps hX hr fun x hx hne => ?_
      rcases List.mem_append.mp hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
      · exact hms x hx
  · split at h
    · subst h
      intro q hq hne hd
      rw [List.mem_singleton.mp (mem_psend hX hq)] at hne hd ⊢
      exact pendOk_propose hne hd rfl rfl rfl
    · subst h; exact outOk_nil hX

/-- What the preamble keeps (`PreEnd`): the outbox, base, log and commit; its term is the message's. -/
theorem preEnd_facts {s s1 : PState} {m : Msg} (h : PreEnd s m s1) :
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
    (h : AppEnd id X m s') : OutOk id w s' := by
  have hrecv : ∀ (q : Msg) (s'' : PState), q.ty = .appResp → q.src = id → q.dst = m.src →
      q.term = m.term → s''.term = m.term →
      (q.reject = false →
        (uint.Z q.index = uint.Z m.index + m.entries.length ∧
          plogTermAt base0 s''.log m.index = some m.logterm ∧
          ∀ (k : Nat) (e : EntryM), m.entries[k]? = some e →
            plogTermAt base0 s''.log (m.index + W64 ((k : Int) + 1)) = some e.Term') ∨
        (uint.Z m.index < uint.Z s''.commit ∧ q.index = s''.commit)) →
      q.dst ≠ id → (∃ j : Fin 3, q.dst = nodeId j) → PendOk id { w with ps := s'' } q := by
    intro q s'' hqt hqs hqd hqtm hst hacc hne hd
    unfold PendOk; rw [hqt]
    exact ⟨hne, hd, hqs, hby, m, hca, hty, hqd, hqtm, hqtm.trans hst.symm, hacc⟩
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
    · show plogTermAt base0 es' m.index = some m.logterm
      rw [hbat m.index (Int.le_refl _) (by have := uint_Z_nonneg m.index; omega)]
      exact plogTermAt_base _ _
    · show plogTermAt base0 es' (m.index + W64 ((k : Int) + 1)) = some e.Term'
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

/-- The type switch's messages (`HandleEnd`) at the state after the preamble, for a message of a
type the network carries. -/
theorem outOk_handle {c : CfgM} {id : w64} {w : NodeView} {s1 s' : PState} {m : Msg}
    (hX : s1.outbox = []) (hb : s1.base = base0) (ht : s1.term = m.term)
    (hby : w.byE = go!"recv") (hca : w.cause = some m) (hpay : m.ty = .app → AppPayloadOk m)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : HandleEnd c id s1 m s') : OutOk id w s' := by
  unfold HandleEnd at h
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
      unfold AppRespEnd at h
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

/-- A received message's step (`RecvEnd`), its term not `0` (`RawNode.Step`'s `NetMsgOk`). -/
theorem outOk_recv {c : CfgM} {id : w64} {w : NodeView} {s s' : PState} {m : Msg}
    (hX : s.outbox = []) (hb : s.base = base0) (hm0 : m.term ≠ W64 0)
    (hby : w.byE = go!"recv") (hca : w.cause = some m) (hpay : m.ty = .app → AppPayloadOk m)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : RecvEnd c id s m s') : OutOk id w s' := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact outOk_nil hX
  · obtain ⟨ho, hb1, -, -, ht⟩ := preEnd_facts hpre
    exact outOk_handle (ho.trans hX) (hb1.trans hb) ht hby hca hpay hsc hh

/-- A tick's messages (`TickEnd`): a campaign's vote requests, a leader's heartbeats. -/
theorem outOk_tick {c : CfgM} {id : w64} {w : NodeView} {s s' : PState}
    (hX : s.outbox = []) (hb : s.base = base0) (h : TickEnd c id s s') : OutOk id w s' := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨hr, ms, hms, rfl⟩
  · exact outOk_nil hX
  · intro q hq hne hd
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
      refine pendOk_vote hne hd rfl rfl rfl rfl rfl ?_ ?_
      · show (plogLast s.base s.log).index' = (plogLast base0 s.log).index'; rw [hb]
      · show (plogLast s.base s.log).term' = (plogLast base0 s.log).term'; rw [hb]
  · intro q hq hne hd
    obtain ⟨hh, hi, hlt, he⟩ := hms q (mem_psend hX hq)
    exact pendOk_heartbeat hne hd hr hh hi hlt he

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
    (hq : SelfMsg id T q) (h : HandleEnd c id s q s1) :
    AdvInv id T c₀ s1 := by
  obtain ⟨-, -, -, hrj, hty⟩ := hq
  unfold HandleEnd at h
  rcases hty with hty | hty <;> rw [hty] at h <;> simp only at h
  · split at h
    · rename_i hr
      unfold AppRespEnd at h
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
          rw [hy'.2 hy'.1.1]; show uint.Z c₀ ≤ uint.Z n; omega
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
          rw [hy'.2 hy'.1.1]; exact hc
      · exact advInv_nil ht hc hX
    · subst h; exact hi

/-- One step of `Advance` (`RecvEnd` of a self-addressed message at the node's term). -/
theorem adv_step {c : CfgM} {id T c₀ : w64} {s s1 : PState} {q : Msg} (hi : AdvInv id T c₀ s)
    (hq : SelfMsg id T q) (h : RecvEnd c id s q s1) :
    AdvInv id T c₀ s1 := by
  have hqt : q.term = s.term := hq.2.2.1.trans hi.1.symm
  rcases h with ⟨-, hh⟩ | ⟨-, hlt, -⟩ | ⟨-, s2, hpre, hh⟩
  · exact adv_handle hi hq hh
  · rw [hqt] at hlt; exact absurd hlt (Int.lt_irrefl _)
  · rcases hpre with ⟨hlt, -⟩ | ⟨-, rfl⟩
    · rw [hqt] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · exact adv_handle hi hq hh

theorem adv_run {c : CfgM} {id T c₀ : w64} {s s' : PState} {qs : List Msg}
    (h : AdvanceEnd c id s qs s') (hq : ∀ q ∈ qs, SelfMsg id T q) (hi : AdvInv id T c₀ s) :
    AdvInv id T c₀ s' := by
  induction h with
  | nil => exact hi
  | cons s s1 s' q qs hr _ ih =>
    exact ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))
      (adv_step hi (hq q (List.mem_cons_self ..)) hr)

/-- `Advance`'s messages (`AdvanceEnd` of self-addressed messages from a state with nothing
queued): a leader's `MsgApp`s, `AppOk` at the end. -/
theorem outOk_advance {c : CfgM} {id : w64} {w : NodeView} {s s' : PState} {qs : List Msg}
    (hX : s.outbox = []) (hq : ∀ q ∈ qs, SelfMsg id s.term q) (h : AdvanceEnd c id s qs s') :
    OutOk id w s' := by
  have hinv : AdvInv id s.term s.commit s' := adv_run h hq (advInv_nil rfl (Int.le_refl _) hX)
  intro x hx hne hd
  obtain ⟨hr, hok, -⟩ := hinv.2.2 x hx
  exact pendOk_app hne hd hr (hok hne).1

/-! ## The `Ready`'s messages -/

/-- **Every message to another voter in the outbox of the state a `Ready` is taken at is
`PendOk`** at the view moved there: one input's at its end state (C1: nothing queued before it),
`Advance`'s a leader's `MsgApp`s (`outOk_advance`). A received `MsgApp`'s batch is `AppPayloadOk`
(C4's `NetShape`: its sender's `AppOk`). -/
theorem outOk_reach {S : AntCheck.State} {net : List Msg} {n : Fin 3} {v : NodeView}
    {ps₁ : PState} (hnet : NetOk S net) (hv : NodeOk S net n v)
    (hr : Reach (nodeId n) net v ps₁) : OutOk (nodeId n) v ps₁ := by
  obtain ⟨hd, -, -, -, hqs, -, -⟩ := hv
  obtain ⟨-, -, -, -, -, -, hX, hb, -⟩ := hd
  cases hr with
  | stay _ => exact outOk_nil hX
  | input inp _ _ hbe hca hm hs =>
    cases inp with
    | recv m =>
      obtain ⟨hmn, -, hm0⟩ := hm m rfl
      exact outOk_recv hX hb hm0 hbe hca (hnet.2.2.1 m hmn).1 (hnet.1 m hmn).1 hs
    | tick => exact outOk_tick hX hb hs
    | propose d => exact outOk_propose hX hs
  | advance _ _ _ _ ha =>
    refine outOk_advance hX (fun q hq => ?_) ha
    obtain ⟨h1, h2, h3, h4, h5⟩ := hqs q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩

/-- **The `Ready`'s messages to other nodes are `PendOk` at the view after it**
(`NodeView.afterReady`), each to a voter (`ReadyOutP`'s `ReadyMsgsToVoters`). -/
theorem pendOk_of_reach {S : AntCheck.State} {net : List Msg} {n : Fin 3} {v : NodeView}
    {ps₁ : PState} {rd : ReadyD} (hnet : NetOk S net) (hv : NodeOk S net n v)
    (hr : Reach (nodeId n) net v ps₁) (hro : ReadyOutP (nodeId n) v ps₁ rd) :
    ∀ q ∈ rd.msgs, PendOk (nodeId n) (v.afterReady ps₁ rd) q := by
  intro q hq
  have hq' := (hro.2.2.2.2.2.2.2.1.mem_iff).mp hq
  rw [List.mem_filter] at hq'
  have hne : q.dst ≠ nodeId n := of_decide_eq_true hq'.2
  exact PendOk.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (outOk_reach hnet hv hr q hq'.1 hne (hro.2.2.2.2.2.2.2.2.2.2.2.2 q hq))

end outbox

end AntSim
end EtcdGrove
end Perennial
