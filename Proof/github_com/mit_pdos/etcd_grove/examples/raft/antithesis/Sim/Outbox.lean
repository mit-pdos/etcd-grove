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

/-! ## `PendOk` per message type -/

/-- `PendOk` reads only the view's role, term, vote, log, base, commit, `Match`, `by` and cause. -/
theorem PendOk.congr {id : w64} {v w : NodeView} {q : Msg} (hr : w.ps.role = v.ps.role)
    (ht : w.ps.term = v.ps.term) (hv : w.ps.vote = v.ps.vote) (hl : w.ps.log = v.ps.log)
    (hb : w.ps.base = v.ps.base) (hc : w.ps.commit = v.ps.commit)
    (hm : w.ps.matched = v.ps.matched) (hbe : w.byE = v.byE) (hca : w.cause = v.cause)
    (h : PendOk N id v q) : PendOk N id w q := by
  unfold PendOk AppOk HeartbeatOk matchOf at *
  rw [hr, ht, hv, hl, hb, hc, hm, hbe, hca]; exact h

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

/-- What the preamble keeps (`PreEnd`): the outbox, base, log and commit; its term is the message's. -/
theorem preEnd_facts {s s1 : PState} {m : Msg} (h : PreEnd kk s m s1) :
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

/-- The type switch's messages (`HandleEnd`) at the state after the preamble, for a message of a
type the network carries. -/
theorem outOk_handle {c : CfgM} {id : w64} {w : NodeView} {s1 s' : PState} {m : Msg}
    (hX : s1.outbox = []) (hb : s1.base = base0) (ht : s1.term = m.term)
    (hby : w.byE = go!"recv") (hca : w.cause = some m) (hpay : m.ty = .app → AppPayloadOk m)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : HandleEnd kk c id s1 m s') : OutOk N id w s' := by
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
    (h : RecvEnd kk c id s m s') : OutOk N id w s' := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact outOk_nil hX
  · obtain ⟨ho, hb1, -, -, ht⟩ := preEnd_facts hpre
    exact outOk_handle (ho.trans hX) (hb1.trans hb) ht hby hca hpay hsc hh

/-- A tick's messages (`TickEnd`): a campaign's vote requests, a leader's heartbeats. -/
theorem outOk_tick {c : CfgM} {id : w64} {w : NodeView} {s s' : PState}
    (hX : s.outbox = []) (hb : s.base = base0) (h : TickEnd kk c id s s') : OutOk N id w s' := by
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
    (hq : SelfMsg id T q) (h : HandleEnd kk c id s q s1) :
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

/-- One step of `Advance` (`RecvEnd` of a self-addressed message at the node's term). -/
theorem adv_step {c : CfgM} {id T c₀ : w64} {s s1 : PState} {q : Msg} (hi : AdvInv id T c₀ s)
    (hq : SelfMsg id T q) (h : RecvEnd kk c id s q s1) :
    AdvInv id T c₀ s1 := by
  have hqt : q.term = s.term := hq.2.2.1.trans hi.1.symm
  rcases h with ⟨-, hh⟩ | ⟨-, hlt, -⟩ | ⟨-, s2, hpre, hh⟩
  · exact adv_handle hi hq hh
  · rw [hqt] at hlt; exact absurd hlt (Int.lt_irrefl _)
  · rcases hpre with ⟨hlt, -⟩ | ⟨-, rfl⟩
    · rw [hqt] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · exact adv_handle hi hq hh

theorem adv_run {c : CfgM} {id T c₀ : w64} {s s' : PState} {qs : List Msg}
    (h : AdvanceEnd kk c id s qs s') (hq : ∀ q ∈ qs, SelfMsg id T q) (hi : AdvInv id T c₀ s) :
    AdvInv id T c₀ s' := by
  induction h with
  | nil => exact hi
  | cons s s1 s' q qs hr _ ih =>
    exact ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))
      (adv_step hi (hq q (List.mem_cons_self ..)) hr)

/-- `Advance`'s messages (`AdvanceEnd` of self-addressed messages from a state with nothing
queued): a leader's `MsgApp`s, `AppOk` at the end. -/
theorem outOk_advance {c : CfgM} {id : w64} {w : NodeView} {s s' : PState} {qs : List Msg}
    (hX : s.outbox = []) (hq : ∀ q ∈ qs, SelfMsg id s.term q) (h : AdvanceEnd kk c id s qs s') :
    OutOk N id w s' := by
  have hinv : AdvInv id s.term s.commit s' := adv_run h hq (advInv_nil rfl (Int.le_refl _) hX)
  intro x hx hne hd
  obtain ⟨hr, hok, -⟩ := hinv.2.2 x hx
  exact pendOk_app (w := w.withP _) hne hd hr (hok hne).1

/-! ## The `Ready`'s messages -/

/-- `Advance` over `RState` is `Advance` over the protocol state at the node's configuration (the
received messages keep the configuration, the storage acknowledgements the protocol state). -/
theorem advanceEndR_toP {Adm : List EntryM → CCState → Prop} {dec : CCDec} {k : NodeK} {id : w64}
    {r r' : RState} {qs : List Msg} (h : AdvanceEndR Adm dec k id r qs r') :
    AdvanceEnd k r.cfg.cfg id r.p qs r'.p := by
  induction h with
  | nil r r' ha =>
    have : r'.p = r.p := by
      rcases ha with rfl | ⟨a, -, rfl⟩ | ⟨j, sn, cs', -, rfl⟩ <;> rfl
    rw [this]; exact .nil _
  | cons r r1 r' q qs hr _ ih =>
    have hc : r1.cfg = r.cfg := hr.2.1.2.2
    rw [hc] at ih
    exact .cons _ _ _ q qs hr.1 ih

/-- **Every message to another voter in the outbox of the state a `Ready` is taken at is
`PendOk`** at the view moved there: one input's at its end state (C1: nothing queued before it),
`Advance`'s a leader's `MsgApp`s (`outOk_advance`). A received `MsgApp`'s batch is `AppPayloadOk`
(C4's `NetShape`: its sender's `AppOk`). For the runs a mask below `mskS4` admits. -/
theorem outOk_reach {msk : SimMask} (hmsk : msk ≤ mskS4) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {xs : List XMsg} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁ xs) : OutOk R.N (nodeId n) v r₁.p := by
  obtain ⟨hmd, _, _, _, _, _, _, hty⟩ := hin.s4 hmsk
  have hX := hv.facts.outbox
  have hb := (hv.facts.snap0 (by rw [hmd])).1
  have hqs := hv.qs
  cases hr with
  | stay _ => exact outOk_nil hX
  | input inp _ _ hinp _ hbe hca _ hm _ hs =>
    rcases Input.inMask_s4 hmsk hinp with ⟨m, rfl⟩ | rfl | ⟨d, rfl⟩
    · obtain ⟨hmn, -, hm0⟩ := hm m rfl
      have h7 := hty m hmn
      exact outOk_recv hX hb hm0 hbe hca (hnet.2.2.1 m hmn).1
        (by rcases h7 with h | h | h | h | h | h | h <;> simp [h]) hs.1.1
    · exact outOk_tick hX hb hs.1.1
    · rcases hs.1.1 with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact outOk_propose hX hh
      · exact absurd rfl h0
      · exact absurd rfl h0
  | advance _ _ _ _ _ _ ha _ =>
    refine outOk_advance hX (fun q hq => ?_) (advanceEndR_toP ha)
    obtain ⟨h1, h2, h3, h4, h5⟩ := hqs q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩

/-- **The `Ready`'s messages to other nodes are `PendOk` at the view after it**
(`NodeView.drainOf`, sync), each to a voter (`ReadyOutP`'s `ReadyMsgsToVoters`). -/
theorem pendOk_of_reach {msk : SimMask} (hmsk : msk ≤ mskS4) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {xs : List XMsg} {rd : ReadyD}
    (hin : InMask msk R net xnet) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁ xs) (hro : ReadyOutP R n v r₁ xs rd) :
    ∀ q ∈ rd.msgs, PendOk R.N (nodeId n) (v.drainOf r₁ rd) q := by
  intro q hq
  have hasync : R.md.async = false := by rw [(hin.s4 hmsk).1]
  have hq' := (((hro.2.2.2.2.2.2.2.2.1 hasync).2).mem_iff).mp hq
  rw [List.mem_filter] at hq'
  have hne : q.dst ≠ nodeId n := of_decide_eq_true hq'.2
  exact PendOk.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (outOk_reach hmsk hin hnet hv hr q hq'.1 hne (hro.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 q (List.mem_append_left _ hq)))

/-- The S4 network's types (`InMask.s4`'s order) in the order of the per-type lemmas. -/
theorem ty7_of_s4 {t : MsgType}
    (h : t = .app ∨ t = .appResp ∨ t = .vote ∨ t = .voteResp ∨ t = .heartbeat ∨ t = .heartbeatResp ∨
      t = .propose) :
    t = .vote ∨ t = .voteResp ∨ t = .app ∨ t = .appResp ∨ t = .heartbeat ∨ t = .heartbeatResp ∨
      t = .propose := by
  rcases h with h | h | h | h | h | h | h <;> simp [h]

/-! ## The leader hint along `Reach` -/

/-- Raft's leader hint at `s` (C1's `LeadOk`): a node that does not lead does not name itself; the
hint is no node or one of the three (`LeadIn`). -/
def LeadHint (N : Nat) (id : w64) (s : PState) : Prop := (s.role ≠ .leader → s.lead ≠ id) ∧ LeadIn N s

theorem leadHint_pre {id : w64} {s s1 : PState} {m : Msg} (h : LeadHint N id s) (hid : id ≠ W64 0)
    (hsrc : fromLeader m.ty = true → m.src ≠ id)
    (hsn : fromLeader m.ty = true → ∃ j : Fin N, m.src = nodeId j) (hp : PreEnd kk s m s1) :
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
    (hh : HandleEnd kk c id s m s') : LeadHint N id s' := by
  unfold HandleEnd at hh
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
    · unfold AppRespEnd at hh
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
    (hr : RecvEnd kk c id s m s') : LeadHint N id s' := by
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
    (ht : TickEnd kk c id s s') : LeadHint N id s' := by
  rcases ht with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
  · exact h
  · exact ⟨fun _ => Ne.symm hid, .inl rfl⟩
  · exact h

theorem leadHint_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg} (h : LeadHint N id s)
    (hid : id ≠ W64 0) (hin : ∃ j : Fin N, id = nodeId j)
    (hq : ∀ q ∈ qs, (q.ty = .appResp ∨ q.ty = .voteResp) ∧ q.src = id)
    (ha : AdvanceEnd kk c id s qs s') : LeadHint N id s' := by
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

/-- **The leader hint is kept along `Reach`** (C1's `LeadOk` at the state a `Ready` is taken at): a
received message is from another node (C4's `NetShape`), one of the servers (`NetOk`), `Advance`
steps only the node's own acknowledgements and vote responses. For the runs a mask below `mskS4`
admits. -/
theorem reach_leadOk {msk : SimMask} (hmsk : msk ≤ mskS4) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {xs : List XMsg} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁ xs) : LeadHint R.N (nodeId n) r₁.p := by
  obtain ⟨_, _, _, _, _, _, _, hty⟩ := hin.s4 hmsk
  have hqs := hv.qs
  have hlo : LeadHint R.N (nodeId n) v.ps := hv.leadOk
  have hid := nodeId_ne_zero n
  have hin' : ∃ j : Fin R.N, nodeId n = nodeId j := ⟨n, rfl⟩
  cases hr with
  | stay _ => exact hlo
  | input inp _ _ hinp _ _ _ _ hm _ hs =>
    rcases Input.inMask_s4 hmsk hinp with ⟨m, rfl⟩ | rfl | ⟨d, rfl⟩
    · obtain ⟨hmn, hmd, -⟩ := hm m rfl
      have hsd : m.src ≠ nodeId n := hmd ▸ (hnet.2.2.1 m hmn).2.1
      obtain ⟨i, hi, -⟩ := (hnet.1 m hmn).2.1
      exact leadHint_recv hlo hid hin' (ty7_of_s4 (hty m hmn)) (.inl hsd) ⟨i, hi⟩ hs.1.1
    · exact leadHint_tick hlo hid hs.1.1
    · rcases hs.1.1 with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact leadHint_propose hlo hh
      · exact absurd rfl h0
      · exact absurd rfl h0
  | advance _ _ _ _ _ _ ha _ =>
    refine leadHint_adv hlo hid hin' (fun q hq => ?_) (advanceEndR_toP ha)
    obtain ⟨h1, -, -, -, h5⟩ := hqs q hq
    exact ⟨h5.imp (fun h => h.1) (fun h => h.1), h1⟩

end outbox

end AntSim
end EtcdGrove
end Perennial
