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
them (an append, a proposal). -/
theorem entsNormal_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hent : m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries) (hl : EntsNormal s.log)
    (h : HandleEnd c id s m s') : EntsNormal s'.log := by
  unfold HandleEnd at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
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
    · unfold AppRespEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩
      · exact hl
      · obtain ⟨ms, -, rfl⟩ := hs; exact hl
      · obtain ⟨ms, -, rfl⟩ := hs; exact hl
    · subst h; exact hl
  · split at h
    · subst h; exact hl
    · subst h; exact hl
  · split at h
    · obtain ⟨ms, -, rfl⟩ := h; exact hl
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

theorem entsNormal_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hent : m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries) (hl : EntsNormal s.log)
    (h : RecvEnd c id s m s') : EntsNormal s'.log := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact entsNormal_handle hsc hent hl hh
  · exact hl
  · obtain ⟨-, -, hl1, -, -⟩ := preEnd_facts hpre
    exact entsNormal_handle hsc hent (hl1 ▸ hl) hh

theorem entsNormal_tick {c : CfgM} {id : w64} {s s' : PState} (hl : EntsNormal s.log)
    (h : TickEnd c id s s') : EntsNormal s'.log := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩ <;> exact hl

theorem entsNormal_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (h : AdvanceEnd c id s qs s') (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp)
    (hl : EntsNormal s.log) : EntsNormal s'.log := by
  induction h with
  | nil => exact hl
  | cons s s1 s' q qs hr _ ih =>
    have hty := hq q (List.mem_cons_self ..)
    refine ih (fun x hx => hq x (List.mem_cons_of_mem _ hx)) (entsNormal_recv ?_ ?_ hl hr)
    · rcases hty with h' | h' <;> simp [h']
    · rintro (h' | h') <;> rcases hty with h'' | h'' <;> rw [h''] at h' <;> cases h'

/-! ## The messages -/

/-- What `msgShape.stmt` says of a message to another node, but a heartbeat's context: a heartbeat
response's context is the cause's, a heartbeat's (`c`). -/
def MShape (id : w64) (c : Option Msg) (q : Msg) : Prop :=
  q.src = id ∧ (NetTy q.ty ∨ q.ty = .propose) ∧ EntsNormal q.entries ∧
  (q.ty = .heartbeatResp → ∃ m, c = some m ∧ m.ty = .heartbeat ∧ q.ctx = m.ctx) ∧
  (q.ty = .heartbeat → q.ctx = [])

/-- Every message of `s`'s outbox to another node is `MShape`. -/
def OutShape (id : w64) (c : Option Msg) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst ≠ id → MShape id c q

theorem outShape_nil {id : w64} {c : Option Msg} {s : PState} (h : s.outbox = []) :
    OutShape id c s := by
  intro q hq; rw [h] at hq; cases hq

theorem outShape_single {id : w64} {c : Option Msg} {X : PState} {q : Msg} (hX : X.outbox = [])
    (hq : MShape id c q) : OutShape id c (psendMsgs X [q]) := by
  intro x hx _
  rw [List.mem_singleton.mp (mem_psend hX hx)]; exact hq

theorem mshape_plain {id d t : w64} {c : Option Msg} {ty : MsgType} {rj : Bool} (hty : NetTy ty)
    (hne : ty ≠ .heartbeatResp) (hne' : ty ≠ .heartbeat) : MShape id c (Msg.plain ty id d t rj) :=
  ⟨rfl, .inl hty, (fun e he => by simp [Msg.plain] at he), (fun h => absurd h hne),
    (fun h => absurd h hne')⟩

theorem mshape_mk {id d t ix lt cm rh : w64} {c : Option Msg} {ty : MsgType} {rj : Bool}
    (hty : NetTy ty) (hne : ty ≠ .heartbeatResp) (hne' : ty ≠ .heartbeat) :
    MShape id c (Msg.mk ty id d t rj ix lt cm rh []) :=
  ⟨rfl, .inl hty, entsNormal_nil, fun h => absurd h hne, fun h => absurd h hne'⟩

/-- An append of the log (`AppOk`). -/
theorem mshape_app {id : w64} {c : Option Msg} {X : PState} {q : Msg} (hl : EntsNormal X.log)
    (h : AppOk id X q) : MShape id c q :=
  ⟨h.2.1, .inl (.inl h.1), fun e he => hl e (h.2.2.2.2.2.2.1 e he),
    (fun h' => by rw [h.1] at h'; cases h'), (fun h' => by rw [h.1] at h'; cases h')⟩

theorem outShape_apps {id : w64} {c : Option Msg} {X : PState} {ms : List Msg}
    (hX : X.outbox = []) (hl : EntsNormal X.log) (hms : ∀ x ∈ ms, x.dst ≠ id → AppOk id X x) :
    OutShape id c (psendMsgs X ms) :=
  fun q hq hne => mshape_app hl (hms q (mem_psend hX hq) hne)

theorem outShape_sends {id : w64} {c : Option Msg} {X s' : PState} (hX : X.outbox = [])
    (hl : EntsNormal s'.log) (h : SendsEnd id X s') : OutShape id c s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact outShape_apps hX hl fun x hx _ => (hms x hx).1

theorem outShape_win {id : w64} {c : Option Msg} {X s' : PState} (hX : X.outbox = [])
    (hl : EntsNormal s'.log) (h : WinEnd id X s') : OutShape id c s' := by
  obtain ⟨mt, ms, -, hms, rfl⟩ := h
  refine outShape_apps hX hl fun x hx hne => ?_
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
  · exact (hms x hx).1

theorem outShape_propose {id : w64} {c : Option Msg} {X s' : PState} {m : Msg}
    (hX : X.outbox = []) (hl : EntsNormal s'.log) (hent : EntsNormal m.entries)
    (h : ProposeEnd id X m s') : OutShape id c s' := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, hms, rfl⟩
    · exact outShape_nil hX
    · refine outShape_apps hX hl fun x hx hne => ?_
      rcases List.mem_append.mp hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
      · exact (hms x hx).1
  · split at h
    · subst h
      exact outShape_single hX ⟨rfl, .inr rfl, hent, (fun h => by cases h), (fun h => by cases h)⟩
    · subst h; exact outShape_nil hX

/-- The type switch's messages at the state after the preamble (nothing queued), the end log
normal. -/
theorem outShape_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hX : s.outbox = [])
    (hl : EntsNormal s'.log)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hent : m.ty = .propose → EntsNormal m.entries)
    (h : HandleEnd c id s m s') : OutShape id (some m) s' := by
  unfold HandleEnd at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact outShape_single hX (mshape_plain (by simp [NetTy]) (by decide) (by decide))
    · exact outShape_single hX (mshape_plain (by simp [NetTy]) (by decide) (by decide))
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, hw⟩ | ⟨-, rfl⟩
      · exact outShape_nil hX
      · exact outShape_win hX hl hw
      · exact outShape_nil hX
    · subst h; exact outShape_nil hX
  · split at h
    · subst h; exact outShape_nil hX
    · rcases h with ⟨-, rfl⟩ | ⟨-, lastnewi, es', -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩ <;>
        exact outShape_single hX (mshape_mk (by simp [NetTy]) (by decide) (by decide))
  · split at h
    · unfold AppRespEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩
      · exact outShape_nil hX
      · exact outShape_sends hX hl hs
      · exact outShape_sends (X := { s with matched := _, commit := n }) hX hl hs
    · subst h; exact outShape_nil hX
  · split at h
    · subst h; exact outShape_nil hX
    · subst h
      exact outShape_single hX ⟨rfl, .inl (by simp [NetTy, Msg.plain]),
        (fun e he => by simp [Msg.plain] at he), (fun _ => ⟨m, rfl, hty, rfl⟩),
        (fun h => by simp [Msg.plain] at h)⟩
  · split at h
    · exact outShape_sends hX hl h
    · subst h; exact outShape_nil hX
  · exact outShape_propose hX hl (hent hty) h

theorem outShape_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hX : s.outbox = [])
    (hm0 : m.term ≠ W64 0) (hl : EntsNormal s'.log)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hent : m.ty = .propose → EntsNormal m.entries)
    (h : RecvEnd c id s m s') : OutShape id (some m) s' := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact outShape_nil hX
  · obtain ⟨ho, -, -, -, -⟩ := preEnd_facts hpre
    exact outShape_handle (ho.trans hX) hl hsc hent hh

/-- **A tick's heartbeats carry no context** (`sendHeartbeat`'s `Context` is the read-only queue's
last request, nil with none: the harness's scope). What `msgShape` needs of `TickEnd` beyond what it
says now (`msgShape_of`). -/
def TickHbCtx : Prop :=
  ∀ (c : CfgM) (id : w64) (s s' : PState), s.outbox = [] → TickEnd c id s s' →
    ∀ q ∈ s'.outbox, q.ty = .heartbeat → q.ctx = []

/-- A tick's messages: vote requests, a leader's heartbeats. -/
theorem outShape_tick {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState} (ht : TickHbCtx)
    (hX : s.outbox = []) (h : TickEnd c id s s') : OutShape id cm s' := by
  have hctx := ht c id s s' hX h
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, hms, rfl⟩
  · exact outShape_nil hX
  · intro q hq hne
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
      exact ⟨rfl, .inl (by simp [NetTy, pvoteReq]), (fun e he => by simp [pvoteReq] at he),
        (fun h => by simp [pvoteReq] at h), (fun h => by simp [pvoteReq] at h)⟩
  · intro q hq _
    obtain ⟨hh, -, -, he, -⟩ := hms q (mem_psend hX hq)
    exact ⟨hh.2.1, .inl (by simp [NetTy, hh.1]), (by rw [he]; exact entsNormal_nil),
      (fun h => by rw [hh.1] at h; cases h), hctx q hq⟩

/-- `Advance`'s messages: a leader's `MsgApp`s of the end log (`adv_run`). -/
theorem outShape_advance {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState} {qs : List Msg}
    (hX : s.outbox = []) (hl : EntsNormal s'.log) (hq : ∀ q ∈ qs, SelfMsg id s.term q)
    (h : AdvanceEnd c id s qs s') : OutShape id cm s' := by
  have hinv : AdvInv id s.term s.commit s' := adv_run h hq (advInv_nil rfl (Int.le_refl _) hX)
  intro x hx hne
  exact mshape_app hl ((hinv.2.2 x hx).2.1 hne).1

/-- **The log and the messages of the state a `Ready` is taken at**: the log normal, every message
to another node `MShape` (the cause's context for a heartbeat response). -/
theorem shape_reach {S : AntCheck.State} {net : List Msg} {n : Fin 3} {v : NodeView}
    {ps₁ : PState} (ht : TickHbCtx) (hnet : NetOk S net) (hv : NodeOk S net n v)
    (hr : Reach (nodeId n) net v ps₁) (hl : EntsNormal v.ps.log)
    (hcm : ∀ m, v.cause = some m → EntsNormal m.entries) :
    EntsNormal ps₁.log ∧ OutShape (nodeId n) v.cause ps₁ := by
  obtain ⟨hd, -, -, -, hqs, -, -⟩ := hv
  obtain ⟨-, -, -, -, -, -, hX, -, -⟩ := hd
  cases hr with
  | stay _ => exact ⟨hl, outShape_nil hX⟩
  | input inp _ _ hbe hca hmm hst =>
    cases inp with
    | recv m =>
      obtain ⟨hmn, -, hm0⟩ := hmm m rfl
      have hsc := (hnet.1 m hmn).1
      have hme := hcm m hca
      have hl' := entsNormal_recv hsc (fun _ => hme) hl hst
      rw [hca]
      exact ⟨hl', outShape_recv hX hm0 hl' hsc (fun _ => hme) hst⟩
    | tick => exact ⟨entsNormal_tick hl hst, outShape_tick ht hX hst⟩
    | propose d =>
      have hpe : EntsNormal (propMsg (nodeId n) d).entries := by
        intro e he; simp only [propMsg, List.mem_singleton] at he; rw [he]
      have hl' : EntsNormal ps₁.log := by
        have h := hst
        simp only [InputStep] at h
        unfold ProposeEnd at h
        split at h
        · rcases h with rfl | ⟨es, ms, hrep, -, rfl⟩
          · exact hl
          · exact entsNormal_append hl (entsNormal_stamp _ _ (entsNormal_propRepl hrep hpe))
        · split at h
          · subst h; exact hl
          · subst h; exact hl
      exact ⟨hl', outShape_propose hX hl' hpe hst⟩
  | advance _ _ _ _ ha =>
    have hl' := entsNormal_adv ha
      (fun q hq => (hqs q hq).2.2.2.2.imp (fun h => h.1) (fun h => h.1)) hl
    refine ⟨hl', outShape_advance hX hl' (fun q hq => ?_) ha⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hqs q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩

/-- **`msgShape.stmt` but a heartbeat's context** (the `Ready`'s messages are the outbox's to other
nodes, `ReadyOutP`): the log normal; every message to another node from the node, of a type the
network carries or a proposal, its entries normal, a heartbeat response's context the handled
heartbeat's. -/
theorem msgShape_core {S : AntCheck.State} {net : List Msg} {n : Fin 3} {v : NodeView}
    {ps₁ : PState} {rd : ReadyD} (ht : TickHbCtx) (hnet : NetOk S net) (hv : NodeOk S net n v)
    (hr : Reach (nodeId n) net v ps₁) (hro : ReadyOutP (nodeId n) v ps₁ rd)
    (hl : EntsNormal v.ps.log) (hcm : ∀ m, v.cause = some m → EntsNormal m.entries) :
    EntsNormal ps₁.log ∧ ∀ q ∈ rd.msgs, MShape (nodeId n) v.cause q := by
  obtain ⟨hl', ho⟩ := shape_reach ht hnet hv hr hl hcm
  refine ⟨hl', fun q hq => ?_⟩
  have hq' := (hro.2.2.2.2.2.2.2.1.mem_iff).mp hq
  rw [List.mem_filter] at hq'
  exact ho q hq'.1 (of_decide_eq_true hq'.2)

/-- **`msgShape.stmt` from `TickHbCtx`**: a heartbeat response echoes the handled heartbeat's
context, `[]` by the premise. -/
theorem msgShape_of (ht : TickHbCtx) : msgShape.stmt := by
  intro S net n v ps₁ rd hnet hv hr hro hl hcm
  obtain ⟨hl', hq⟩ := msgShape_core ht hnet hv hr hro hl (fun m h => (hcm m h).1)
  refine ⟨hl', fun q hmem => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq q hmem
  refine ⟨h1, h2, fun hh => ?_, h3⟩
  rcases hh with hh | hh
  · exact h5 hh
  · obtain ⟨m, hc, hmt, hx⟩ := h4 hh
    rw [hx]; exact (hcm m hc).2 hmt

/-- **A tick's heartbeats carry no context** (`TickEnd`'s heartbeat arm). -/
theorem tickHbCtx : TickHbCtx := by
  intro c id s s' hX h q hq hty
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, hms, rfl⟩
  · rw [hX] at hq; cases hq
  · rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hty; simp [Msg.plain] at hty
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq; simp [pvoteReq] at hty
  · exact (hms q (mem_psend hX hq)).2.2.2.2

/-- **`msgShape.stmt`**. -/
theorem msgShape : msgShape.stmt := msgShape_of tickHbCtx

end shape

end AntSim
end EtcdGrove
end Perennial
