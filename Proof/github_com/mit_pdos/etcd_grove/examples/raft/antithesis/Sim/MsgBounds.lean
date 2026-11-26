/-
Lean-first (no Rocq counterpart).

# A `Ready`'s messages' numbers (#33 S4, drain)

`outNums_reach`: every message a `Ready` hands to another node (a forwarded proposal or read
request too: its
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
variable {cf : CfgM} {kk : NodeK}

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

/-! ## The read requests' messages -/

/-- Entries' terms and indices below `K`. -/
def EntNums (K : Int) (es : List EntryM) : Prop := ∀ e ∈ es, uint.Z e.Term' < K ∧ uint.Z e.Index' < K

/-- A leader's read requests' numbers below `K`: the deferred ones' entries (their contexts), the
queued ones' indices (the commit index each is answered at) and entries. -/
def ReadNums (K : Int) (s : PState) : Prop :=
  (∀ p ∈ s.rd.pend, EntNums K p.2) ∧
    (s.role = .leader → ∀ r ∈ s.rd.ro.pending, uint.Z r.index < K ∧ EntNums K r.ents)

theorem outNums_out {K : Int} {id : w64} {s t : PState} {ms : List Msg} (hX : OutNums K id s)
    (ho : t.outbox = s.outbox ++ ms) (hms : ∀ q ∈ ms, q.dst ≠ id → MsgNums K q) : OutNums K id t := by
  intro q hq hne
  rw [ho] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hX q hq hne
  · exact hms q hq hne

theorem StateNums.of_keep {K : Int} {s t : PState} (hk : PKeep s t) (h : StateNums K t) :
    StateNums K s := by
  unfold StateNums at *; rw [hk.base, hk.log, hk.commit] at h; exact h

theorem outNums_sends' {K : Int} {id : w64} {X s' : PState} (hX : OutNums K id X)
    (hs : StateNums K s') (h : SendsEnd cf id X s') : OutNums K id s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact outNums_out hX rfl fun x hx _ => appOk_nums (s := X) hs (hms x hx).1

/-- A read request's answer: its request's index and entries, no log term or commit. -/
theorem msgNums_resp {K : Int} (hK : 0 < K) {id T : w64} {qs : List ReadReq} {q : Msg}
    (h : RespMsg id T qs q) (hq : ∀ r ∈ qs, uint.Z r.index < K ∧ EntNums K r.ents) : MsgNums K q := by
  obtain ⟨-, -, -, -, -, hlt, hc, r, hr, -, hi, he⟩ := h
  have h0 : uint.Z (W64 0) = 0 := rfl
  exact ⟨by rw [hi]; exact (hq r hr).1, by rw [hlt, h0]; exact hK, by rw [hc, h0]; exact hK,
    by rw [he]; exact (hq r hr).2⟩

/-- A leader's heartbeat: no index, log term or entries, its commit at most the state's. -/
theorem msgNums_hb {K : Int} (hK : 0 < K) {c : CfgM} {id : w64} {s : PState} {q : Msg}
    (h : HbSendOk c id s q) (hc : uint.Z s.commit < K) : MsgNums K q := by
  obtain ⟨⟨-, -, -, -, hqc, -⟩, hi, hlt, he, -⟩ := h
  have h0 : uint.Z (W64 0) = 0 := rfl
  exact ⟨by rw [hi, h0]; exact hK, by rw [hlt, h0]; exact hK, by omega, by rw [he]; simp⟩

/-- A read request's messages (`ReadIdxEnd`): heartbeats, the answer at the commit index, the
forward of the request (its numbers). -/
theorem outNums_readIdx {K : Int} {id : w64} {s s' : PState} {m : Msg} (hX : OutNums K id s)
    (hK : 0 < K) (hc : uint.Z s.commit < K) (hm : MsgNums K m) (h : ReadIdxEnd cf id s m s') :
    OutNums K id s' := by
  obtain ⟨ms, -, ho, hms⟩ := readIdxEnd_out h
  refine outNums_out hX ho fun q hq _ => ?_
  rcases hms q hq with ⟨-, hh⟩ | hh | ⟨-, -, rfl⟩
  · exact msgNums_hb hK hh hc
  · exact msgNums_resp hK hh fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨hc, hm.2.2.2⟩
  · exact hm

/-- A commit's release: heartbeats and the deferred requests' answers at the commit index. -/
theorem outNums_release {K : Int} {id : w64} {X s2 : PState} (hX : OutNums K id X) (hK : 0 < K)
    (hc : uint.Z X.commit < K) (hp : ∀ p ∈ X.rd.pend, EntNums K p.2) (h : ReleaseEnd cf id X s2) :
    OutNums K id s2 := by
  obtain ⟨ms, -, ho, hms⟩ := releaseEnd_out h
  refine outNums_out hX ho fun q hq _ => ?_
  rcases hms q hq with hh | hh
  · exact msgNums_hb hK hh hc
  · refine msgNums_resp hK hh fun r hr => ?_
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
    exact ⟨hc, hp p hp'⟩

/-- A read acknowledgement: answers of the leader's queued requests. -/
theorem outNums_readAck {K : Int} {id : w64} {s s' : PState} {m : Msg} (hX : OutNums K id s)
    (hK : 0 < K) (hro : ∀ r ∈ s.rd.ro.pending, uint.Z r.index < K ∧ EntNums K r.ents)
    (h : ReadAckEnd cf id s m s') : OutNums K id s' := by
  obtain ⟨ms, qs, -, ho, hsub, hms⟩ := readAckEnd_out h
  exact outNums_out hX ho fun q hq _ => msgNums_resp hK (hms q hq) fun r hr => hro r (hsub r hr)

/-- The type switch's messages at the state after the preamble, the handled message within `K`
(all its numbers for a proposal or a read request), a leader's read requests' (`ReadNums`). -/
theorem outNums_handle {K : Int} {c : CfgM} {id : w64} {s1 s' : PState} {m : Msg}
    (hX : s1.outbox = []) (hb : s1.base = base0) (hs : StateNums K s') (hm : InNums K m)
    (hpay : m.ty = .app → AppPayloadOk m) (hsc : RdTy m.ty)
    (hmp : m.ty = .propose ∨ m.ty = .readIndex → MsgNums K m) (hrq : ReadNums K s1)
    (h : HandleEndO kk c id s1 m s') : OutNums K id s' := by
  have hK := hs.1
  unfold HandleEndO at h
  rcases hsc with hs4 | hty | hty
  rotate_left
  · rw [hty] at h; simp only at h
    refine outNums_readIdx (outNums_nil hX) hK ?_ (hmp (.inr hty)) h
    rw [← (readIdxEnd_keep h).commit]; exact hs.2.2.2.1
  · rw [hty] at h; simp only at h
    split at h
    · rcases h with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact outNums_nil hX
    · subst h; exact outNums_nil hX
  rcases ty7_of_s4 hs4 with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
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
    · rename_i hr
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs'⟩ | ⟨-, x, n, -, -, hs'⟩ | ⟨-, x, n, s2, -, -, hrel, hs'⟩
      · exact outNums_nil hX
      · exact outNums_sends hX hs hs'
      · exact outNums_sends (X := { s1 with matched := _, commit := n }) hX hs hs'
      · have hc2 : s'.commit = s2.commit := by obtain ⟨ms, -, rfl⟩ := hs'; rfl
        refine outNums_sends' (outNums_release ?_ hK ?_ ?_ hrel) hs hs'
        · exact outNums_nil hX
        · rw [← (releaseEnd_keep hrel).commit, ← hc2]; exact hs.2.2.2.1
        · exact hrq.1
    · subst h; exact outNums_nil hX
  · split at h
    · subst h; exact outNums_nil hX
    · subst h
      intro q hq _
      rw [List.mem_singleton.mp (mem_psend hX hq)]
      exact msgNums_plain hK .heartbeatResp id m.src s1.term false
  · split at h
    · rename_i hr
      obtain ⟨s2, hs', ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact outNums_sends hX hs hs'
      · have hrd2 : s2.rd = s1.rd := by obtain ⟨ms, -, rfl⟩ := hs'; rfl
        refine outNums_readAck (outNums_sends hX (StateNums.of_keep (readAckEnd_keep ha) hs) hs') hK
          (fun r hr' => ?_) ha
        rw [hrd2] at hr'; exact hrq.2 hr r hr'
    · subst h; exact outNums_nil hX
  · exact outNums_propose hX hs (hmp (.inl hty)) h

/-- A received message's step (`RecvEndO`), its term not `0` but a forwarded read request's. -/
theorem outNums_recv {K : Int} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hX : s.outbox = []) (hb : s.base = base0) (hs : StateNums K s')
    (hm : InNums K m) (hpay : m.ty = .app → AppPayloadOk m) (hsc : RdTy m.ty)
    (hmp : m.ty = .propose ∨ m.ty = .readIndex → MsgNums K m) (hrq : ReadNums K s)
    (h : RecvEndO kk c id s m s') : OutNums K id s' := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact outNums_handle hX hb hs hm hpay hsc hmp hrq hh
  · exact outNums_nil hX
  · obtain ⟨ho, hb1, -, -, -⟩ := preEnd_facts hpre
    refine outNums_handle (ho.trans hX) (hb1.trans hb) hs hm hpay hsc hmp ?_ hh
    rcases hpre with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨hrq.1, fun h' => by simp [pbecomeFollower] at h'⟩
    · exact hrq

/-- A tick's messages: a campaign's vote requests (the last entry id), a leader's heartbeats. -/
theorem outNums_tick {K : Int} {c : CfgM} {id : w64} {s s' : PState}
    (hX : s.outbox = []) (hb : s.base = base0) (hs : StateNums K s') (h : TickEndO kk c id s s') :
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

/-- A (pre-)vote request carries the last entry id of a log within `K`. -/
theorem msgNums_voteReq {K : Int} {id d t : w64} {s : PState} {cl : List w8} (hK : 0 < K)
    (hb : s.base = base0) (hl : ∀ e ∈ s.log, uint.Z e.Term' < K ∧ uint.Z e.Index' < K) :
    MsgNums K (pvoteReq id d t (plogLast s.base s.log) cl) := by
  have h0 : uint.Z (W64 0) = 0 := rfl
  unfold MsgNums pvoteReq
  simp only [List.not_mem_nil, false_implies, implies_true, and_true, h0, hK]
  rw [hb]
  unfold plogLast
  split
  · rename_i e he
    have := hl e (List.mem_of_getLast? he)
    exact ⟨this.2, this.1⟩
  · exact ⟨hK, hK⟩

/-- A campaign's messages (`CampaignSends`): its vote requests (the last entry id). -/
theorem outNums_campaignSends {K : Int} {c : CfgM} {id : w64} {X s' : PState} {cl : List w8}
    (hX : X.outbox = []) (hb : X.base = base0) (hs : StateNums K s') (h : CampaignSends c id X cl s') :
    OutNums K id s' := by
  obtain ⟨peers, -, rfl⟩ := h
  intro q hq hne
  rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
  · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
  · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
    exact msgNums_voteReq hs.1 hb hs.2.2.2.2

/-- A received message's new arm (`RecvEndP`): empty answers, pre-vote answers with no payload, a
campaign's requests. -/
theorem outNums_recvP {K : Int} {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hX : s.outbox = []) (hb : s.base = base0) (hs : StateNums K s') (h : RecvEndP kk c id s m s') :
    OutNums K id s' := by
  have hK := hs.1
  have hz : uint.Z (W64 0) < K := hK
  rcases h with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, ⟨-, -, rfl⟩ | ⟨-, rfl⟩⟩ |
      ⟨-, -, -, rfl⟩ | ⟨-, rfl | ⟨-, -, -, hcs⟩⟩
  · intro q hq _
    rw [List.mem_singleton.mp (mem_psend hX hq)]
    exact ⟨hz, hz, hz, fun e he => by cases he⟩
  · intro q hq _
    rw [List.mem_singleton.mp (mem_psend hX hq)]; exact msgNums_plain hK _ _ _ _ _
  · exact outNums_nil hX
  · intro q hq _
    rw [List.mem_singleton.mp (mem_psend hX hq)]; exact msgNums_plain hK _ _ _ _ _
  · intro q hq _
    rw [List.mem_singleton.mp (mem_psend hX hq)]; exact msgNums_plain hK _ _ _ _ _
  · exact outNums_nil (s := pbecomeFollower s _ _) hX
  · exact outNums_nil hX
  · exact outNums_campaignSends hX hb hs hcs

/-- A tick's new arm (`TickEndP`): a pre-campaign's pre-vote requests (the last entry id). -/
theorem outNums_tickP {K : Int} {c : CfgM} {id : w64} {s s' : PState}
    (hX : s.outbox = []) (hb : s.base = base0) (hs : StateNums K s') (h : TickEndP kk c id s s') :
    OutNums K id s' := by
  rcases h with ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, rfl⟩
  · intro q hq hne
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
      exact msgNums_voteReq (id := id) (d := d) (t := s.term + W64 1) (cl := []) hs.1 hb hs.2.2.2.2
  · exact outNums_nil (s := pbecomeFollower s _ _) hX

/-- What `Advance`'s steps keep within `K`: the read answers queued (a release's, at the commit
index then) and the deferred requests' entries. -/
def AdvNums (K : Int) (id : w64) (s : PState) : Prop :=
  (∀ q ∈ s.outbox, q.dst ≠ id → q.ty = .readIndexResp → MsgNums K q) ∧
    ∀ p ∈ s.rd.pend, EntNums K p.2

theorem releaseEnd_pend {c : CfgM} {id : w64} {X s2 : PState} (h : ReleaseEnd c id X s2) :
    s2.rd.pend = [] := by
  rcases h with ⟨-, hb, -, rfl⟩ | ⟨-, rfl⟩
  · rfl
  · exact (preadRespondAll_rd id _ _).1

theorem advNums_sends {K : Int} {id : w64} {X s' : PState} (hX : AdvNums K id X)
    (h : SendsEnd cf id X s') : AdvNums K id s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  refine ⟨fun q hq hne hty => ?_, hX.2⟩
  rw [psendMsgs_outbox] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hX.1 q hq hne hty
  · rw [(hms q hq).1.1] at hty; cases hty

/-- One step of `Advance` (a self-acknowledgement or self-vote at the node's term): the commit
raised at most, and `AdvNums` kept when the step's commit is within `K` (a release's answers are
at it). -/
theorem advNums_step {K : Int} {c : CfgM} {id T : w64} {s s1 : PState} {q : Msg} (hK : 0 < K)
    (hT : s.term = T) (hq : SelfMsg id T q) (h : RecvEndO kk c id s q s1) :
    uint.Z s.commit ≤ uint.Z s1.commit ∧
      (AdvNums K id s → uint.Z s1.commit < K → AdvNums K id s1) := by
  have hqt' : q.term = s.term := hq.2.2.1.trans hT.symm
  have hh : HandleEndO kk c id s q s1 := by
    rcases h with ⟨-, hh⟩ | ⟨-, hlt, -⟩ | ⟨-, s2, hpre, hh⟩
    · exact hh
    · rw [hqt'] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · rcases hpre with ⟨hlt, -⟩ | ⟨-, rfl⟩
      · rw [hqt'] at hlt; exact absurd hlt (Int.lt_irrefl _)
      · exact hh
  obtain ⟨-, -, -, -, hty⟩ := hq
  unfold HandleEndO at hh
  rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, hn, hs⟩ | ⟨-, x, n, s2, -, hn, hrel, hs⟩
      · exact ⟨Int.le_refl _, fun hi _ => hi⟩
      · have hc' : s1.commit = s.commit := by obtain ⟨ms, -, rfl⟩ := hs; rfl
        exact ⟨by rw [hc']; exact Int.le_refl _, fun hi _ => advNums_sends hi hs⟩
      · have hc' : s1.commit = n := by obtain ⟨ms, -, rfl⟩ := hs; rfl
        refine ⟨?_, fun hi _ => advNums_sends (X := { s with matched := _, commit := n }) hi hs⟩
        rw [hc']
        rcases hn with rfl | hn
        · exact Int.le_refl _
        · exact Int.le_of_lt hn.1
      · have hk := releaseEnd_keep hrel
        have hc' : s1.commit = n := by obtain ⟨ms, -, rfl⟩ := hs; exact hk.commit
        refine ⟨by rw [hc']; exact Int.le_of_lt hn.1, fun hi hc => advNums_sends ?_ hs⟩
        obtain ⟨ms, -, ho, hms⟩ := releaseEnd_out hrel
        refine ⟨fun q hq hne hqt => ?_, fun p hp => by rw [releaseEnd_pend hrel] at hp; cases hp⟩
        rw [ho] at hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hi.1 q hq hne hqt
        · rcases hms q hq with hh | hh
          · rw [hh.1.1] at hqt; cases hqt
          · refine msgNums_resp hK hh fun r hr => ?_
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
            exact ⟨show uint.Z n < K by rw [← hc']; exact hc, hi.2 p hp⟩
    · subst hh; exact ⟨Int.le_refl _, fun hi _ => hi⟩
  · split at hh
    · rcases hh with ⟨-, rfl⟩ | ⟨-, mt, ms, -, hms, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨Int.le_refl _, fun hi _ => hi⟩
      · refine ⟨Int.le_refl _, fun hi _ => ⟨fun y hy hne hyt => ?_, hi.2⟩⟩
        rw [psendMsgs_outbox] at hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hi.1 y hy hne hyt
        · rcases List.mem_append.mp hy with hy | hy
          · rw [List.mem_singleton.mp hy] at hne; exact absurd (pselfAck_dst id _) hne
          · rw [(hms y hy).1.1] at hyt; cases hyt
      · exact ⟨Int.le_refl _, fun hi _ => hi⟩
    · subst hh; exact ⟨Int.le_refl _, fun hi _ => hi⟩

theorem advNums_run {K : Int} {c : CfgM} {id T c₀ : w64} {s s' : PState} {qs : List Msg}
    (hK : 0 < K) (h : AdvanceEndO kk c id s qs s') (hq : ∀ q ∈ qs, SelfMsg id T q)
    (hv : AdvInv id T c₀ s) :
    uint.Z s.commit ≤ uint.Z s'.commit ∧ (AdvNums K id s → uint.Z s'.commit < K → AdvNums K id s') := by
  induction h with
  | nil => exact ⟨Int.le_refl _, fun h _ => h⟩
  | cons s s1 s' q qs hr _ ih =>
    have hq0 := hq q (List.mem_cons_self ..)
    obtain ⟨c1, f1⟩ := advNums_step hK hv.1 hq0 hr
    obtain ⟨c2, f2⟩ := ih (fun x hx => hq x (List.mem_cons_of_mem _ hx)) (adv_step hv hq0 hr)
    exact ⟨Int.le_trans c1 c2, fun ha hc => f2 (f1 ha (Int.lt_of_le_of_lt c2 hc)) hc⟩

/-- `Advance`'s messages (`AdvanceEndO` of self-addressed messages from a state with nothing
queued): a leader's `MsgApp`s (`AppOk` at the end), heartbeats, and the deferred requests'
answers (`AdvNums`). -/
theorem outNums_advance {K : Int} {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (hX : s.outbox = []) (hs : StateNums K s') (hp : ∀ p ∈ s.rd.pend, EntNums K p.2)
    (hq : ∀ q ∈ qs, SelfMsg id s.term q)
    (h : AdvanceEndO kk c id s qs s') : OutNums K id s' := by
  have hinv : AdvInv id s.term s.commit s' := adv_run h hq (advInv_nil rfl (Int.le_refl _) hX)
  have hn := (advNums_run hs.1 h hq (advInv_nil rfl (Int.le_refl _) hX)).2
    ⟨(fun q hq' => by rw [hX] at hq'; cases hq'), hp⟩ hs.2.2.2.1
  have h0 : uint.Z (W64 0) = 0 := rfl
  intro x hx hne
  obtain ⟨-, hok, -⟩ := hinv.2.2 x hx
  rcases hok hne with ⟨ha, -⟩ | ⟨hh, hi, hlt, he⟩ | ⟨hty, -, -⟩
  · exact appOk_nums hs ha
  · obtain ⟨-, -, -, -, hqc, -⟩ := hh
    have := hs.2.2.2.1
    exact ⟨by rw [hi, h0]; exact hs.1, by rw [hlt, h0]; exact hs.1, by omega, by rw [he]; simp⟩
  · exact hn.1 x hx hne hty

theorem msgNums_readMsg {K : Int} (hK : 0 < K) (d : List w8) : MsgNums K (readMsg d) := by
  have h0 : uint.Z (W64 0) = 0 := rfl
  refine ⟨?_, ?_, ?_, fun e he => ?_⟩
  · show uint.Z (W64 0) < K; omega
  · show uint.Z (W64 0) < K; omega
  · show uint.Z (W64 0) < K; omega
  · simp only [readMsg, List.mem_singleton] at he; subst he
    exact ⟨show uint.Z (W64 0) < K by omega, show uint.Z (W64 0) < K by omega⟩

/-- **`OutNums` along `ReachP`**: every message to another node is within any bound `K` the end
state's numbers, the handled message's index and log term (all its numbers for a read request,
which a follower forwards and a leader answers with its entries) and the view's read requests'
(`ReadNums`) are within. -/
theorem outNums_reachP {K : Int} {c : CfgM} {id : w64} {net : List Msg} {xnet : List XMsg} {v : NodeView} {ps₁ : PState}
    (hX : v.ps.outbox = []) (hb : v.ps.base = base0) (hs : StateNums K ps₁)
    (hpay : ∀ m ∈ net, m.ty = .app → AppPayloadOk m)
    (hm : ∀ m, v.cause = some m → InNums K m ∧ m.ty ≠ .propose ∧ (m.ty = .readIndex → MsgNums K m))
    (hrq : ReadNums K v.ps)
    (hqs : ∀ q ∈ v.qs, q.ty ≠ .preVoteResp → SelfMsg id v.ps.term q)
    (hr : ReachP kk c id net xnet v ps₁) : OutNums K id ps₁ := by
  cases hr with
  | stay _ => exact outNums_nil hX
  | recv m _ _ _ hca hmn _ _ hty h =>
    exact outNums_recv hX hb hs (hm m hca).1 (hpay m hmn) hty
      (fun hp => hp.elim (fun hp => absurd hp (hm m hca).2.1) (hm m hca).2.2) hrq h
  | recvP m _ _ _ _ _ _ _ _ h => exact outNums_recvP hX hb hs h
  | tick _ _ _ h => exact outNums_tick hX hb hs h
  | tickP _ _ _ h => exact outNums_tickP hX hb hs h
  | propose d _ _ _ h => exact outNums_propose hX hs (msgNums_propMsg hs.1 _ d) h
  | read d _ _ _ hh =>
    refine outNums_readIdx (outNums_nil hX) hs.1 ?_ (msgNums_readMsg hs.1 d) hh
    rw [← (readIdxEnd_keep hh).commit]; exact hs.2.2.2.1
  | advance _ _ _ _ hno h =>
    exact outNums_advance hX hs hrq.1 (fun q hq => hqs q hq (hno q hq)) h
  | advP _ _ _ _ _ _ _ h =>
    rcases h with rfl | ⟨-, -, hcs⟩
    · exact outNums_nil hX
    · exact outNums_campaignSends hX hb hs hcs
  | sends _ _ _ _ h => exact outNums_sends hX hs h
  | adoptX x _ _ _ _ _ _ => exact outNums_nil (s := pbecomeFollower v.ps _ _) hX
  | campX x p1 _ _ _ _ _ _ _ hp1 hc =>
    rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      exact outNums_campaignSends (by exact hX) (by exact hb) hs hc.sends

/-- **The numbers of the messages of the state a `Ready` is taken at** (`outNums_reachP`): every
message to another node is within any bound `K` the state's numbers (`StateNums`), the handled
message's index and log term (`InNums`, of the drain's cause, which is no proposal: the network
carries none, `NetFacts`; all its numbers for a read request) and the view's read requests'
(`ReadNums`) are within. For the runs a mask below `mskB1` admits. -/
theorem outNums_reach {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {K : Int}
    (hin : InMask msk R net xnet) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) (hs : StateNums K r₁.p)
    (hm : ∀ m, v.cause = some m → InNums K m ∧ m.ty ≠ .propose ∧ (m.ty = .readIndex → MsgNums K m))
    (hrq : ReadNums K v.ps) : OutNums K (nodeId n) r₁.p := by
  obtain ⟨hmd, -⟩ := hin.b1 hmsk
  refine outNums_reachP hv.facts.outbox (hv.facts.snap0 (by rw [hmd])).1 hs
    (fun m hmn => (hnet.2.2.1 m hmn).1) hm hrq (fun q hq hne => ?_) (ReachIn.toP hmsk hin hnet hv hr)
  obtain ⟨h1, h2, h3, h4, h5⟩ := (hv.qs q hq).notPre hne
  exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩

/-- **The `Ready`'s messages within `K`** (`ReadyOutP`: in sync mode they are the outbox's to other
nodes). -/
theorem readyMsgNums {msk : SimMask} (hmsk : msk ≤ mskB1) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {rd : ReadyD} {K : Int}
    (hin : InMask msk R net xnet) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) (hro : ReadyOutP R n v r₁ rd)
    (hs : StateNums K r₁.p)
    (hm : ∀ m, v.cause = some m → InNums K m ∧ m.ty ≠ .propose ∧ (m.ty = .readIndex → MsgNums K m))
    (hrq : ReadNums K v.ps) :
    ∀ q ∈ rd.msgs ++ rd.resp, MsgNums K q := by
  have hasync : R.md.async = false := by rw [(hin.b1 hmsk).1]
  obtain ⟨hresp, hmsg⟩ := hro.2.2.2.2.2.2.2.2.1 hasync
  intro q hq
  rw [hresp, List.append_nil] at hq
  have hq' := (hmsg.mem_iff).mp hq
  rw [List.mem_filter] at hq'
  exact outNums_reach hmsk hin hnet hv hr hs hm hrq q hq'.1 (of_decide_eq_true hq'.2)

end bounds

end AntSim
end EtcdGrove
end Perennial
