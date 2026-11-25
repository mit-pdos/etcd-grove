/-
Lean-first (no Rocq counterpart).

# A `Ready`'s messages' numbers (#33 S4, drain)

`outNums_reach`: every message a `Ready` hands to another node (a forwarded proposal too: its
`send` report reads its numbers, though `Cluster.send` drops it; its numbers are the proposal's,
`propMsg`'s zeros), taken at the state `ps₁` the node reached (`Reach`), has its index, log term,
commit and entries' terms and indices below any bound `K` that `ps₁`'s own numbers are below
(`StateNums`: its last index, commit and log entries' terms and indices) and the handled message's
are (`MsgNums`). What `NetFacts` (`< 2 ^ 61`) and the `send` report's `numBound` ask of a message;
the harness gets `StateNums` from raft's log records' receipts (`DrainBounds.lean`).

Per input, as `Outbox.lean`'s `outOk_reach`: a vote request carries the last entry id; responses
to a vote or a heartbeat carry no number; an acknowledgement carries the batch's last index (an entry
of the end state's log), the commit index (stale), or the handled append's index with a hint term
below its log term (a rejection); an append is `AppOk` at the end state (`plogTermAt` of its log,
its entries the log's, its commit at most the state's); a heartbeat's commit is at most the state's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Outbox

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap

section bounds
variable [GooseExts]
variable {cf : CfgM}

/-- A message's numbers the binding reads, below `K`: its index, log term and commit, its entries'
terms and indices. (Its term is bounded by raft's term budget, `Hmsgs_term`.) -/
def MsgNums (K : Int) (q : Msg) : Prop :=
  uint.Z q.index < K ∧ uint.Z q.logterm < K ∧ uint.Z q.commit < K ∧
  ∀ e ∈ q.entries, uint.Z e.Term' < K ∧ uint.Z e.Index' < K

/-- A state's numbers below `K`: no snapshot, its last index and commit, its entries' terms and
indices; `K` positive. -/
def StateNums (K : Int) (s : PState) : Prop :=
  0 < K ∧ s.base = base0 ∧ plogLastIndexZ base0 s.log < K ∧ uint.Z s.commit < K ∧
  ∀ e ∈ s.log, uint.Z e.Term' < K ∧ uint.Z e.Index' < K

/-- What the answers read of the handled message: its index and log term below `K` (a rejection
echoes the index, its hint term is at most the log term; an acceptance's index is the batch's end). -/
def InNums (K : Int) (m : Msg) : Prop := uint.Z m.index < K ∧ uint.Z m.logterm < K

/-- Every message of `s`'s outbox to another node is `MsgNums K`. -/
def OutNums (K : Int) (id : w64) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst ≠ id → MsgNums K q

theorem outNums_nil {K : Int} {id : w64} {s : PState} (h : s.outbox = []) : OutNums K id s := by
  intro q hq; rw [h] at hq; cases hq

/-- `StateNums` reads nothing of the outbox. -/
theorem stateNums_psend {K : Int} {s : PState} {ms : List Msg} :
    StateNums K (psendMsgs s ms) ↔ StateNums K s := Iff.rfl

/-- A message with no payload. -/
theorem msgNums_plain {K : Int} (hK : 0 < K) (ty : MsgType) (src dst term : w64) (rj : Bool) :
    MsgNums K (Msg.plain ty src dst term rj) := by
  unfold MsgNums Msg.plain
  simp only [List.not_mem_nil, false_implies, implies_true, and_true]
  have : uint.Z (W64 0) = 0 := rfl
  simp only [this]; omega

/-- A term the log has at an index (`plogTermAt` from `base0`) is the base's `0` or an entry's. -/
theorem plogTermAt_lt {K : Int} {l : List EntryM} {i t : w64} (hK : 0 < K)
    (hl : ∀ e ∈ l, uint.Z e.Term' < K) (h : plogTermAt base0 l i = some t) : uint.Z t < K := by
  unfold plogTermAt at h
  split at h
  · cases h
  split at h
  · cases h; show uint.Z (W64 0) < K; exact hK
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact hl e (List.mem_of_getElem? he)

/-- An index the log has a term at is at most its last index. -/
theorem plogTermAt_le {l : List EntryM} {i t : w64} (h : plogTermAt base0 l i = some t) :
    uint.Z i ≤ plogLastIndexZ base0 l :=
  (plogTermAt_some_range _ _ _ _ h).2

/-- An append `AppOk` at a state within `K`. -/
theorem appOk_nums {K : Int} {id : w64} {s : PState} {q : Msg} (hs : StateNums K s)
    (h : AppOk id s q) : MsgNums K q := by
  obtain ⟨hK, hb, hli, hc, hl⟩ := hs
  obtain ⟨-, -, -, -, ht, hqc, he, -, -⟩ := h
  rw [hb] at ht
  exact ⟨by have := plogTermAt_le ht; omega, plogTermAt_lt hK (fun e he => (hl e he).1) ht,
    by omega, fun e h' => hl e (he e h')⟩

/-- `MsgApp`s `AppOk` at `X` (`SendsEnd`'s, the broadcast after a win or a proposal). -/
theorem outNums_apps {K : Int} {id : w64} {X : PState} {ms : List Msg} (hX : X.outbox = [])
    (hs : StateNums K X) (hms : ∀ x ∈ ms, x.dst ≠ id → AppOk id X x) :
    OutNums K id (psendMsgs X ms) :=
  fun q hq hne => appOk_nums hs (hms q (mem_psend hX hq) hne)

theorem outNums_sends {K : Int} {id : w64} {X s' : PState} (hX : X.outbox = [])
    (hs : StateNums K s') (h : SendsEnd cf id X s') : OutNums K id s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact outNums_apps hX hs fun x hx _ => (hms x hx).1

theorem outNums_win {K : Int} {id : w64} {X s' : PState} (hX : X.outbox = [])
    (hs : StateNums K s') (h : WinEnd cf id X s') : OutNums K id s' := by
  obtain ⟨mt, ms, -, hms, rfl⟩ := h
  refine outNums_apps hX hs fun x hx hne => ?_
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
  · exact (hms x hx).1

/-- A proposal's numbers within `K` (`propMsg`'s are zeros). -/
theorem msgNums_propMsg {K : Int} (hK : 0 < K) (id : w64) (d : List w8) :
    MsgNums K (propMsg id d) := by
  have h0 : uint.Z (W64 0) = 0 := rfl
  refine ⟨?_, ?_, ?_, fun e he => ?_⟩
  · show uint.Z (W64 0) < K; omega
  · show uint.Z (W64 0) < K; omega
  · show uint.Z (W64 0) < K; omega
  · simp only [propMsg, List.mem_singleton] at he; subst he
    exact ⟨show uint.Z (W64 0) < K by omega, show uint.Z (W64 0) < K by omega⟩

/-- A proposal's step: its replication (`AppOk`), or its forwarding (the proposal's numbers,
`hm`). -/
theorem outNums_propose {K : Int} {id : w64} {X s' : PState} {m : Msg} (hX : X.outbox = [])
    (hs : StateNums K s') (hm : MsgNums K m) (h : ProposeEnd cf id X m s') : OutNums K id s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, hms, rfl⟩
    · exact outNums_nil hX
    · refine outNums_apps hX hs fun x hx hne => ?_
      rcases List.mem_append.mp hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
      · exact (hms x hx).1
  · split at h
    · subst h
      intro q hq _
      rw [List.mem_singleton.mp (mem_psend hX hq)]
      exact ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩
    · subst h; exact outNums_nil hX

/-- `handleAppendEntries`'s answer at `X` (the sender adopted), the handled append within `K`. -/
theorem outNums_appEnd {K : Int} {id : w64} {X s' : PState} {m : Msg} (hX : X.outbox = [])
    (hb : X.base = base0) (hs : StateNums K s') (hm : InNums K m) (hpay : AppPayloadOk m)
    (h : AppEnd id X m s') : OutNums K id s' := by
  have hK := hs.1
  have hz : uint.Z (W64 0) < K := hK
  rcases h with ⟨-, rfl⟩ | ⟨-, lastnewi, es', hma, rfl⟩ |
      ⟨-, -, hint, hintterm, -, hht, rfl⟩
  · intro q hq _
    rw [List.mem_singleton.mp (mem_psend hX hq)]
    exact ⟨hs.2.2.2.1, hz, hz, fun e he => by cases he⟩
  · intro q hq _
    rw [List.mem_singleton.mp (mem_psend hX hq)]
    refine ⟨?_, hz, hz, fun e he => by cases he⟩
    show uint.Z lastnewi < K
    rw [hb] at hma
    obtain ⟨hwf, hnw⟩ := hpay
    obtain ⟨-, hli, -⟩ := plogMaybeAppend_inv _ _ _ _ _ _ hwf hnw hma
    have hbat := plogMaybeAppend_batch _ _ _ _ _ _ hwf hnw hma
    simp only at hli hbat hnw
    have hlog : plogLastIndexZ base0 es' < K := hs.2.2.1
    by_cases hn : m.entries.length = 0
    · rw [hli, hn]; have := hm.1; push_cast; omega
    · -- the batch's last entry is in the new log at `lastnewi`
      have hlen : 0 < m.entries.length := Nat.pos_of_ne_zero hn
      have hj := hbat lastnewi (by omega) (by omega)
      have hsome : (plogTermAt base0 es' lastnewi).isSome := by
        rw [hj]
        unfold plogTermAt
        simp only
        rw [if_neg (by omega), if_neg (by omega)]
        have hk : (uint.Z lastnewi - uint.Z m.index - 1).toNat < m.entries.length := by omega
        rw [List.getElem?_eq_getElem hk]; rfl
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
      have := plogTermAt_le ht
      omega
  · intro q hq _
    rw [List.mem_singleton.mp (mem_psend hX hq)]
    refine ⟨hm.1, by show uint.Z hintterm < K; have := hm.2; omega, hz, fun e he => by cases he⟩

/-- The type switch's messages at the state after the preamble, the handled message within `K`. -/
theorem outNums_handle {K : Int} {c : CfgM} {id : w64} {s1 s' : PState} {m : Msg}
    (hX : s1.outbox = []) (hb : s1.base = base0) (hs : StateNums K s') (hm : InNums K m)
    (hpay : m.ty = .app → AppPayloadOk m)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose) (hmp : m.ty = .propose → MsgNums K m)
    (h : HandleEnd c id s1 m s') : OutNums K id s' := by
  have hK := hs.1
  unfold HandleEnd at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · intro q hq _
      rw [List.mem_singleton.mp (mem_psend hX hq)]; exact msgNums_plain hK _ _ _ _ _
    · intro q hq _
      rw [List.mem_singleton.mp (mem_psend hX hq)]; exact msgNums_plain hK _ _ _ _ _
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact outNums_nil hX
      · exact outNums_win hX hs hw
      · exact outNums_nil hX
    · subst h; exact outNums_nil hX
  · split at h
    · subst h; exact outNums_nil hX
    · exact outNums_appEnd (X := padoptLeader s1 m.src) hX hb hs hm (hpay hty) h
  · split at h
    · unfold AppRespEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs'⟩ | ⟨-, x, n, -, -, hs'⟩
      · exact outNums_nil hX
      · exact outNums_sends hX hs hs'
      · exact outNums_sends (X := { s1 with matched := _, commit := n }) hX hs hs'
    · subst h; exact outNums_nil hX
  · split at h
    · subst h; exact outNums_nil hX
    · subst h
      intro q hq _
      rw [List.mem_singleton.mp (mem_psend hX hq)]
      exact msgNums_plain hK .heartbeatResp id m.src s1.term false
  · split at h
    · exact outNums_sends hX hs h
    · subst h; exact outNums_nil hX
  · exact outNums_propose hX hs (hmp hty) h

/-- A received message's step (`RecvEnd`), its term not `0`. -/
theorem outNums_recv {K : Int} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hX : s.outbox = []) (hb : s.base = base0) (hm0 : m.term ≠ W64 0) (hs : StateNums K s')
    (hm : InNums K m) (hpay : m.ty = .app → AppPayloadOk m)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose) (hmp : m.ty = .propose → MsgNums K m)
    (h : RecvEnd c id s m s') : OutNums K id s' := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact outNums_nil hX
  · obtain ⟨ho, hb1, -, -, -⟩ := preEnd_facts hpre
    exact outNums_handle (ho.trans hX) (hb1.trans hb) hs hm hpay hsc hmp hh

/-- A tick's messages: a campaign's vote requests (the last entry id), a leader's heartbeats. -/
theorem outNums_tick {K : Int} {c : CfgM} {id : w64} {s s' : PState}
    (hX : s.outbox = []) (hb : s.base = base0) (hs : StateNums K s') (h : TickEnd c id s s') :
    OutNums K id s' := by
  have hK := hs.1
  have h0 : uint.Z (W64 0) = 0 := rfl
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, hms, rfl⟩
  · exact outNums_nil hX
  · intro q hq hne
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
      -- the log is the tick's state's (`pbecomeCandidate` keeps it)
      have hl : ∀ e ∈ s.log, uint.Z e.Term' < K ∧ uint.Z e.Index' < K := hs.2.2.2.2
      unfold MsgNums pvoteReq
      simp only [List.not_mem_nil, false_implies, implies_true, and_true, h0, hK]
      rw [hb]
      unfold plogLast
      split
      · rename_i e he
        have := hl e (List.mem_of_getLast? he)
        exact ⟨this.2, this.1⟩
      · exact ⟨hK, hK⟩
  · intro q hq _
    obtain ⟨hh, hi, hlt, he, -⟩ := hms q (mem_psend hX hq)
    obtain ⟨-, -, -, -, hc, -⟩ := hh
    refine ⟨by rw [hi, h0]; exact hK, by rw [hlt, h0]; exact hK, ?_, by rw [he]; simp⟩
    have := hs.2.2.2.1
    show uint.Z q.commit < K
    simp only [psendMsgs] at this
    omega

/-- `Advance`'s messages: a leader's `MsgApp`s, `AppOk` at the end (`adv_run`). -/
theorem outNums_advance {K : Int} {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (hX : s.outbox = []) (hs : StateNums K s') (hq : ∀ q ∈ qs, SelfMsg id s.term q)
    (h : AdvanceEnd c id s qs s') : OutNums K id s' := by
  have hinv : AdvInv id s.term s.commit s' := adv_run h hq (advInv_nil rfl (Int.le_refl _) hX)
  intro x hx hne
  exact appOk_nums hs ((hinv.2.2 x hx).2.1 hne).1

/-- **The numbers of the messages of the state a `Ready` is taken at**: every message to another
node but a forwarded proposal is within any bound `K` the state's numbers (`StateNums`) and the
handled message's index and log term (`InNums`, of the drain's cause, which is no proposal: the
network carries none, `NetFacts`) are within. -/
theorem outNums_reach {S : AntCheck.State} {net : List Msg} {n : Fin 3} {v : NodeView}
    {ps₁ : PState} {K : Int} (hnet : NetOk S net) (hv : NodeOk S net n v)
    (hr : Reach (nodeId n) net v ps₁) (hs : StateNums K ps₁)
    (hm : ∀ m, v.cause = some m → InNums K m ∧ m.ty ≠ .propose) : OutNums K (nodeId n) ps₁ := by
  obtain ⟨hd, -, -, -, hqs, -, -⟩ := hv
  obtain ⟨-, -, -, -, -, -, hX, hb, -⟩ := hd
  cases hr with
  | stay _ => exact outNums_nil hX
  | input inp _ _ hbe hca hmm hst =>
    cases inp with
    | recv m =>
      obtain ⟨hmn, -, hm0⟩ := hmm m rfl
      exact outNums_recv hX hb hm0 hs (hm m hca).1 (hnet.2.2.1 m hmn).1 (hnet.1 m hmn).1
        (fun hp => absurd hp (hm m hca).2) hst
    | tick => exact outNums_tick hX hb hs hst
    | propose d => exact outNums_propose hX hs (msgNums_propMsg hs.1 _ d) hst
  | advance _ _ _ _ ha =>
    refine outNums_advance hX hs (fun q hq => ?_) ha
    obtain ⟨h1, h2, h3, h4, h5⟩ := hqs q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩

/-- **The `Ready`'s messages within `K`** (`ReadyOutP`: they are the outbox's to other nodes). -/
theorem readyMsgNums {S : AntCheck.State} {net : List Msg} {n : Fin 3} {v : NodeView}
    {ps₁ : PState} {rd : ReadyD} {K : Int} (hnet : NetOk S net) (hv : NodeOk S net n v)
    (hr : Reach (nodeId n) net v ps₁) (hro : ReadyOutP (nodeId n) v ps₁ rd)
    (hs : StateNums K ps₁) (hm : ∀ m, v.cause = some m → InNums K m ∧ m.ty ≠ .propose) :
    ∀ q ∈ rd.msgs, MsgNums K q := by
  intro q hq
  have hq' := (hro.2.2.2.2.2.2.2.1.mem_iff).mp hq
  rw [List.mem_filter] at hq'
  exact outNums_reach hnet hv hr hs hm q hq'.1 (of_decide_eq_true hq'.2)

end bounds

end AntSim
end EtcdGrove
end Perennial
