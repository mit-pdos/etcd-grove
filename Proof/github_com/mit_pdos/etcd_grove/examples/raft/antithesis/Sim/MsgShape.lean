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
`TickEndO` (`Protocol/InputEnd.lean`) says in its heartbeat arm (`x.ctx = []`, lifted from
`stepLeader`'s exact context, `hbCtx`, `[]` with no read request pending, the RawNode scope's):
`tickHbCtx`, and `msgShape := msgShape_of tickHbCtx`.

`dst_reach` (#33 S4, destinations): every message of the state a `Ready` is taken at to another
node is to one of the three (`DstIn`): a response to the handled message's sender (a node,
`NetOk`), a leader's appends and heartbeats to the configuration's peers (`AppSendOk`'s and
`TickEndO`'s `c.ids`, `cfgM3`'s the three), a campaign's requests to the voters, a forwarded proposal
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
them (an append, a proposal). -/
theorem entsNormal_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg}
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (hent : m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries) (hl : EntsNormal s.log)
    (h : HandleEndO kk c id s m s') : EntsNormal s'.log := by
  unfold HandleEndO at h
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
    · unfold AppRespEndO at h
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
    (h : RecvEndO kk c id s m s') : EntsNormal s'.log := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact entsNormal_handle hsc hent hl hh
  · exact hl
  · obtain ⟨-, -, hl1, -, -⟩ := preEnd_facts hpre
    exact entsNormal_handle hsc hent (hl1 ▸ hl) hh

theorem entsNormal_tick {c : CfgM} {id : w64} {s s' : PState} (hl : EntsNormal s.log)
    (h : TickEndO kk c id s s') : EntsNormal s'.log := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩ <;> exact hl

theorem entsNormal_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg}
    (h : AdvanceEndO kk c id s qs s') (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp)
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
def MShape (md : RnMode) (id : w64) (c : Option Msg) (q : Msg) : Prop :=
  q.src = id ∧ (NetTy md q.ty ∨ q.ty = .propose) ∧ EntsNormal q.entries ∧
  (q.ty = .heartbeatResp → ∃ m, c = some m ∧ m.ty = .heartbeat ∧ q.ctx = m.ctx) ∧
  (q.ty = .heartbeat → q.ctx = [])

/-- Without reads an `MShape` heartbeat or response has no context: a response echoes the handled
heartbeat's, which (on the network) has none (`MsgMask`). -/
theorem mshape_ctx {R : RunCfg} {S : AntCheck.State} {net : List Msg} {id : w64} {c : Option Msg}
    {q : Msg} (hnet : NetOk R S net) (hc : ∀ m, c = some m → m ∈ net) (hq : MShape R.md id c q) :
    R.md.reads = false → (q.ty = .heartbeat ∨ q.ty = .heartbeatResp) → q.ctx = [] := by
  intro hrd hh
  rcases hh with hh | hh
  · exact hq.2.2.2.2 hh
  · obtain ⟨m, hcm, hmt, hx⟩ := hq.2.2.2.1 hh
    rw [hx]; exact (hnet.2.2.2.2 m (hc m hcm)).2.2.2 hrd (.inl hmt)

/-- Every message of `s`'s outbox to another node is `MShape`. -/
def OutShape (md : RnMode) (id : w64) (c : Option Msg) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst ≠ id → MShape md id c q

theorem outShape_nil {id : w64} {c : Option Msg} {s : PState} (h : s.outbox = []) :
    OutShape md id c s := by
  intro q hq; rw [h] at hq; cases hq

theorem outShape_single {id : w64} {c : Option Msg} {X : PState} {q : Msg} (hX : X.outbox = [])
    (hq : MShape md id c q) : OutShape md id c (psendMsgs X [q]) := by
  intro x hx _
  rw [List.mem_singleton.mp (mem_psend hX hx)]; exact hq

theorem mshape_plain {id d t : w64} {c : Option Msg} {ty : MsgType} {rj : Bool} (hty : NetTy md ty)
    (hne : ty ≠ .heartbeatResp) (hne' : ty ≠ .heartbeat) : MShape md id c (Msg.plain ty id d t rj) :=
  ⟨rfl, .inl hty, (fun e he => by simp [Msg.plain] at he), (fun h => absurd h hne),
    (fun h => absurd h hne')⟩

theorem mshape_mk {id d t ix lt cm rh : w64} {c : Option Msg} {ty : MsgType} {rj : Bool}
    (hty : NetTy md ty) (hne : ty ≠ .heartbeatResp) (hne' : ty ≠ .heartbeat) :
    MShape md id c (Msg.mk ty id d t rj ix lt cm rh []) :=
  ⟨rfl, .inl hty, entsNormal_nil, fun h => absurd h hne, fun h => absurd h hne'⟩

/-- An append of the log (`AppOk`). -/
theorem mshape_app {id : w64} {c : Option Msg} {X : PState} {q : Msg} (hl : EntsNormal X.log)
    (h : AppOk id X q) : MShape md id c q :=
  ⟨h.2.1, .inl (.inl h.1), fun e he => hl e (h.2.2.2.2.2.2.1 e he),
    (fun h' => by rw [h.1] at h'; cases h'), (fun h' => by rw [h.1] at h'; cases h')⟩

theorem outShape_apps {id : w64} {c : Option Msg} {X : PState} {ms : List Msg}
    (hX : X.outbox = []) (hl : EntsNormal X.log) (hms : ∀ x ∈ ms, x.dst ≠ id → AppOk id X x) :
    OutShape md id c (psendMsgs X ms) :=
  fun q hq hne => mshape_app hl (hms q (mem_psend hX hq) hne)

theorem outShape_sends {id : w64} {c : Option Msg} {X s' : PState} (hX : X.outbox = [])
    (hl : EntsNormal s'.log) (h : SendsEnd cf id X s') : OutShape md id c s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact outShape_apps hX hl fun x hx _ => (hms x hx).1

theorem outShape_win {id : w64} {c : Option Msg} {X s' : PState} (hX : X.outbox = [])
    (hl : EntsNormal s'.log) (h : WinEnd cf id X s') : OutShape md id c s' := by
  obtain ⟨mt, ms, -, hms, rfl⟩ := h
  refine outShape_apps hX hl fun x hx hne => ?_
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.mem_singleton] at hx; subst hx; exact absurd (pselfAck_dst id _) hne
  · exact (hms x hx).1

theorem outShape_propose {id : w64} {c : Option Msg} {X s' : PState} {m : Msg}
    (hX : X.outbox = []) (hl : EntsNormal s'.log) (hent : EntsNormal m.entries)
    (h : ProposeEnd cf id X m s') : OutShape md id c s' := by
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
    (h : HandleEndO kk c id s m s') : OutShape md id (some m) s' := by
  unfold HandleEndO at h
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
    · unfold AppRespEndO at h
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
    (h : RecvEndO kk c id s m s') : OutShape md id (some m) s' := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hm0
  · exact outShape_nil hX
  · obtain ⟨ho, -, -, -, -⟩ := preEnd_facts hpre
    exact outShape_handle (ho.trans hX) hl hsc hent hh

/-- A tick's messages: vote requests, a leader's heartbeats (their context `hbCtx` of the read-only
queue, empty when no read request is pending at a leader, `hro`). -/
theorem outShape_tick {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState}
    (hro : s.role = .leader → s.rd.ro.pending = []) (hX : s.outbox = []) (h : TickEndO kk c id s s') :
    OutShape md id cm s' := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨hr, ms, hms, rfl⟩
  · exact outShape_nil hX
  · intro q hq hne
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, -, rfl⟩ := List.mem_map.mp hq
      exact ⟨rfl, .inl (by simp [NetTy, pvoteReq]), (fun e he => by simp [pvoteReq] at he),
        (fun h => by simp [pvoteReq] at h), (fun h => by simp [pvoteReq] at h)⟩
  · intro q hq _
    obtain ⟨hh, -, -, he, hc, -⟩ := hms q (mem_psend hX hq)
    exact ⟨hh.2.1, .inl (by simp [NetTy, hh.1]), (by rw [he]; exact entsNormal_nil),
      (fun h => by rw [hh.1] at h; cases h), fun _ => by rw [hc]; simp [hbCtx, hro hr]⟩

/-- `Advance`'s messages: a leader's `MsgApp`s of the end log (`adv_run`). -/
theorem outShape_advance {c : CfgM} {id : w64} {cm : Option Msg} {s s' : PState} {qs : List Msg}
    (hX : s.outbox = []) (hl : EntsNormal s'.log) (hq : ∀ q ∈ qs, SelfMsg id s.term q)
    (h : AdvanceEndO kk c id s qs s') : OutShape md id cm s' := by
  have hinv : AdvInv id s.term s.commit s' := adv_run h hq (advInv_nil rfl (Int.le_refl _) hX)
  intro x hx hne
  exact mshape_app hl ((hinv.2.2 x hx).2.1 hne).1

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

/-- **The ghost prefix is kept along `Reach`** (for the runs a mask below `mskB1a` admits: no
snapshot is received). -/
theorem reach_fp {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    r₁.fp = v.r.fp := by
  obtain ⟨_, _, _, _, _, _, _, hty⟩ := hin.b1a hmsk
  cases hr with
  | stay _ => rfl
  | input inp _ hinp _ _ _ _ hm _ hs =>
    rcases Input.step_b1a hmsk hin hinp hs with ⟨m, rfl⟩ | ⟨-, hs⟩ | ⟨d, rfl⟩
    · obtain ⟨hmn, -, -⟩ := hm m rfl
      exact recvEndR_fp hs (by rcases hty m hmn with h | h | h | h | h | h | h <;> rw [h] <;> decide)
    · exact hs.2.2.1
    · exact recvEndR_fp hs (by simp [propMsg])
  | advance _ _ _ _ _ _ ha _ =>
    refine advanceEndR_fp ha fun q hq => ?_
    rcases ((hv.qs q hq).2.2.2.2).imp (fun h => h.1) (fun h => h.1) with h | h <;> rw [h] <;> decide

/-! ## The shape along `Reach` -/

theorem entsNormal_full {r : RState} (h : EntsNormal r.full) : EntsNormal r.fp ∧ EntsNormal r.p.log :=
  ⟨fun e he => h e (List.mem_append_left _ he), fun e he => h e (List.mem_append_right _ he)⟩

/-- **The log and the messages of the state a `Ready` is taken at**: the full log normal, every
message to another node `MShape` (the cause's context for a heartbeat response). For the runs a mask
below `mskB1a` admits; a leader with no read request pending (`hro`). -/
theorem shape_reach {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) (hfl : EntsNormal v.r.full)
    (hro : v.ps.role = .leader → v.ps.rd.ro.pending = [])
    (hcm : ∀ m, v.cause = some m → m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries) :
    EntsNormal r₁.full ∧ OutShape R.md (nodeId n) v.cause r₁.p := by
  obtain ⟨_, _, _, _, _, _, _, hty⟩ := hin.b1a hmsk
  have hX := hv.facts.outbox
  have hqs := hv.qs
  have hfp := reach_fp hmsk hin hv hr
  obtain ⟨hf0, hl⟩ := entsNormal_full hfl
  have hfull : ∀ {l : List EntryM}, EntsNormal l → EntsNormal (r₁.fp ++ l) := fun hl' =>
    entsNormal_append (hfp ▸ hf0) hl'
  cases hr with
  | stay _ => exact ⟨hfl, outShape_nil hX⟩
  | input inp _ hinp _ hbe hca _ hmm _ hst =>
    rcases Input.step_b1a hmsk hin hinp hst with ⟨m, rfl⟩ | ⟨-, hst⟩ | ⟨d, rfl⟩
    · obtain ⟨hmn, -, hm0⟩ := hmm m rfl
      have hsc := ty7_of_s4 (hty m hmn)
      have hme := hcm m hca
      have hl' := entsNormal_recv hsc hme hl (RecvEnd.toO_in hmsk hin hnet hv hmn hst.1)
      rw [hca]
      exact ⟨hfull hl', outShape_recv hX hm0 hl' hsc (fun h => hme (.inr h)) (RecvEnd.toO_in hmsk hin hnet hv hmn hst.1)⟩
    · exact ⟨hfull (entsNormal_tick hl (TickEnd.toO_in hmsk hin hst.1)), outShape_tick hro hX (TickEnd.toO_in hmsk hin hst.1)⟩
    · have hpe : EntsNormal (propMsg (nodeId n) d).entries := by
        intro e he; simp only [propMsg, List.mem_singleton] at he; rw [he]
      rcases (RecvEnd.toO_prop hmsk hin hv hst.1) with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · have hl' := entsNormal_handle (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
          (fun _ => hpe) hl hh
        exact ⟨hfull hl', outShape_propose hX hl' hpe hh⟩
      · exact absurd rfl h0
      · exact absurd rfl h0
  | advance _ _ _ _ _ _ ha _ =>
    have ha' := advanceEndR_toO hmsk hin hv ha
    have hl' := entsNormal_adv ha'
      (fun q hq => (hqs q hq).2.2.2.2.imp (fun h => h.1) (fun h => h.1)) hl
    refine ⟨hfull hl', outShape_advance hX hl' (fun q hq => ?_) ha'⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hqs q hq
    exact ⟨h1, h2, h3, h4, h5.imp (fun h => h.1) (fun h => h.1)⟩

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

/-- The type switch's messages go to the sender (a server), a leader's appends to the
configuration's peers, a forwarded proposal to the leader (a server, `LeadIn`). -/
theorem dstIn_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hc : CfgIn N c)
    (hX : DstIn N id s) (hl : LeadIn N s) (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : HandleEndO kk c id s m s') : DstIn N id s' := by
  unfold HandleEndO at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
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
    · unfold AppRespEndO at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩
      · exact hX
      · exact dstIn_sends hc hs hX
      · exact dstIn_sends hc hs hX
    · subst h; exact hX
  · split at h
    · subst h; exact hX
    · subst h; exact dstIn_one rfl hX rfl hsn
  · split at h
    · exact dstIn_sends hc h hX
    · subst h; exact hX
  · exact dstIn_propose hc hl h hX

theorem dstIn_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hc : CfgIn N c)
    (hX : DstIn N id s) (hl : LeadIn N s) (hsn : ∃ j : Fin N, m.src = nodeId j)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : RecvEndO kk c id s m s') : DstIn N id s' := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact dstIn_handle hc hX hl hsn hsc hh
  · exact hX
  · have ho := (preEnd_facts hpre).1
    have hl1 : LeadIn N s1 := by
      rcases hpre with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · show (if fromLeader m.ty then m.src else W64 0) = W64 0 ∨
          ∃ j : Fin N, (if fromLeader m.ty then m.src else W64 0) = nodeId j
        split
        · exact .inr hsn
        · exact .inl rfl
      · exact hl
    exact dstIn_handle hc (fun q hq => hX q (ho ▸ hq)) hl1 hsn hsc hh

theorem dstIn_tick {c : CfgM} {id : w64} {s s' : PState} (hc : CfgIn N c) (hX : s.outbox = [])
    (h : TickEndO kk c id s s') : DstIn N id s' := by
  rcases h with rfl | ⟨-, -, peers, cl, hp, rfl⟩ | ⟨-, ms, hms, rfl⟩
  · exact dstIn_nil hX
  · intro q hq hne
    rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
    · rw [List.mem_singleton.mp hq] at hne; exact absurd rfl hne
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      have hd' : d ∈ elements (c.voters \ {[id]}) := hp.mem_iff.mp hd
      rw [GMap.elem_of_elements, GMap.elem_of_difference] at hd'
      exact hc _ ((GMap.elem_of_union _ _ _).2 (.inl hd'.1))
  · intro q hq _
    exact hc _ (hms q (mem_psend hX hq)).2.2.2.2.2

/-- `Advance`'s steps (the node's own acknowledgements and vote responses) keep `DstIn` and the
leader hint. -/
theorem dstIn_adv {c : CfgM} {R : RunCfg} {n : Fin R.N} {s s' : PState} {qs : List Msg} (hc : CfgIn R.N c)
    (hX : DstIn R.N (nodeId n) s) (hl : LeadHint R.N (nodeId n) s)
    (hq : ∀ q ∈ qs, (q.ty = .appResp ∨ q.ty = .voteResp) ∧ q.src = nodeId n)
    (ha : AdvanceEndO kk c (nodeId n) s qs s') : DstIn R.N (nodeId n) s' := by
  induction ha with
  | nil => exact hX
  | cons s s1 s' q qs hr _ ih =>
    have hq0 := hq q (List.mem_cons_self ..)
    have hsc : q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨
        q.ty = .heartbeat ∨ q.ty = .heartbeatResp ∨ q.ty = .propose := by
      rcases hq0.1 with h0 | h0
      · exact .inr (.inr (.inr (.inl h0)))
      · exact .inr (.inl h0)
    exact ih (dstIn_recv hc hX hl.2 ⟨n, hq0.2⟩ hsc hr)
      (leadHint_recv hl (nodeId_ne_zero n) ⟨n, rfl⟩ hsc (.inr hq0.1) ⟨n, hq0.2⟩ hr)
      (fun x hx => hq x (List.mem_cons_of_mem _ hx))

/-- **The destinations of the messages of the state a `Ready` is taken at**: every one to another
node is to a server. For the runs a mask below `mskB1a` admits (the initial configuration). -/
theorem dst_reach {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁) : DstIn R.N (nodeId n) r₁.p := by
  obtain ⟨hmd, _, _, _, _, _, _, hty⟩ := hin.b1a hmsk
  have hX := hv.facts.outbox
  have hqs := hv.qs
  have hlo : LeadHint R.N (nodeId n) v.ps := hv.leadOk
  have hc : CfgIn R.N v.r.cfg.cfg := by
    rw [(hv.facts.conf0 (by rw [hmd])).1]; exact cfgIn_voters0 R
  cases hr with
  | stay _ => exact dstIn_nil hX
  | input inp _ hinp _ _ _ _ hm _ hs =>
    rcases Input.step_b1a hmsk hin hinp hs with ⟨m, rfl⟩ | ⟨-, hs⟩ | ⟨d, rfl⟩
    · obtain ⟨hmn, -, -⟩ := hm m rfl
      obtain ⟨i, hi, -⟩ := (hnet.1 m hmn).2.1
      exact dstIn_recv hc (dstIn_nil hX) hlo.2 ⟨i, hi⟩ (ty7_of_s4 (hty m hmn)) (RecvEnd.toO_in hmsk hin hnet hv hmn hs.1)
    · exact dstIn_tick hc hX (TickEnd.toO_in hmsk hin hs.1)
    · rcases (RecvEnd.toO_prop hmsk hin hv hs.1) with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact dstIn_propose hc hlo.2 hh (dstIn_nil hX)
      · exact absurd rfl h0
      · exact absurd rfl h0
  | advance _ _ _ _ _ _ ha _ =>
    refine dstIn_adv hc (dstIn_nil hX) hlo (fun q hq => ?_) (advanceEndR_toO hmsk hin hv ha)
    obtain ⟨h1, -, -, -, h5⟩ := hqs q hq
    exact ⟨h5.imp (fun h => h.1) (fun h => h.1), h1⟩

/-- **`msgShape.stmt` but a heartbeat's context** (the `Ready`'s messages are the outbox's to other
nodes, `ReadyOutP`): the full log normal; every message to another node from the node, of a type the
network carries or a proposal, its entries normal, a heartbeat response's context the handled
heartbeat's. -/
theorem msgShape_core {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {ms : List Msg}
    (hin : InMask msk R net xnet) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁)
    (hmsg : ms.Perm (r₁.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n))))
    (hfl : EntsNormal v.r.full) (hro : v.ps.role = .leader → v.ps.rd.ro.pending = [])
    (hcm : ∀ m, v.cause = some m → m.ty = .app ∨ m.ty = .propose → EntsNormal m.entries) :
    EntsNormal r₁.full ∧ ∀ q ∈ ms, MShape R.md (nodeId n) v.cause q := by
  obtain ⟨hl', ho⟩ := shape_reach hmsk hin hnet hv hr hfl hro hcm
  refine ⟨hl', fun q hq => ?_⟩
  have hq' := (hmsg.mem_iff).mp hq
  rw [List.mem_filter] at hq'
  exact ho q hq'.1 (of_decide_eq_true hq'.2)

/-- **`msgShape.stmt`'s conclusion over `ReachIn`**, for the runs a mask below `mskB1a` admits, a
leader with no read request pending (`hro`): a heartbeat response echoes the handled heartbeat's
context, `[]` by the premise; the destinations by `dst_reach`. -/
theorem msgShape_in_of {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} {rd : ReadyD}
    (hin : InMask msk R net xnet) (hnet : NetOk R S net) (hv : NodeOk R dec S net n v)
    (hr : ReachIn msk R dec Adm net xnet n v r₁)
    (hmsg : (rd.msgs ++ rd.resp).Perm (r₁.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n))))
    (hfl : EntsHarness v.r.full) (hro : v.ps.role = .leader → v.ps.rd.ro.pending = [])
    (hcm : ∀ m, v.cause = some m → EntsHarness m.entries ∧
      (R.md.reads = false → m.ty = .heartbeat → m.ctx = [])) :
    EntsHarness r₁.full ∧ (∀ q ∈ rd.msgs ++ rd.resp, ReadyMsgShape R.md (nodeId n) q) ∧
      ReadyMsgsToVoters R.N rd := by
  obtain ⟨hl', hq⟩ := msgShape_core hmsk hin hnet hv hr hmsg hfl hro (fun m h _ => (hcm m h).1)
  have hds := dst_reach hmsk hin hnet hv hr
  refine ⟨hl', fun q hmem => ?_, fun q hmem => ?_⟩
  rotate_left
  · have hq' := (hmsg.mem_iff).mp hmem
    rw [List.mem_filter] at hq'
    exact hds q hq'.1 (of_decide_eq_true hq'.2)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq q hmem
  refine ⟨h1, h2, fun hrd hh => ?_, h3⟩
  rcases hh with hh | hh
  · exact h5 hh
  · obtain ⟨m, hc, hmt, hx⟩ := h4 hh
    rw [hx]; exact (hcm m hc).2 hrd hmt

/-- **`msgShape.stmt` over `ReachIn`**, for the runs a mask below `mskB1a` admits: `msgShape_in_of`,
a leader having no read request pending without reads (`NodeFacts.roPend`). -/
theorem msgShape_in (msk : SimMask) (hmsk : msk ≤ mskB1a) :
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
  have hrd : R.md.reads = false := by rw [(hin.b1a hmsk).1]
  exact msgShape_in_of hmsk hin hnet hv hr hmsg hfl (hv.facts.roPend hrd) hcm


/-! ## What `Reach` keeps (the masks below `mskB1a`) -/

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

/-- The type switch keeps `RoOk`: every arm keeps the read-only queue and the role, makes the node
a follower, or makes it leader (`pbecomeLeader` resets the queue). -/
theorem roOk_handle {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hs : RoOk s)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : HandleEndO kk c id s m s') : RoOk s' := by
  unfold HandleEndO at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
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
    · unfold AppRespEndO at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs'⟩ | ⟨-, x, n, -, -, hs'⟩
      · exact hs
      · exact roOk_sends hs' hs
      · exact roOk_sends hs' hs
    · subst h; exact hs
  · split at h
    · subst h; exact hs
    · subst h; exact ⟨hs.1, fun h => by simp [psendMsgs, padoptLeader] at h⟩
  · split at h
    · exact roOk_sends h hs
    · subst h; exact hs
  · exact roOk_propose h hs

theorem roOk_recv {c : CfgM} {id : w64} {s s' : PState} {m : Msg} (hs : RoOk s)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp ∨ m.ty = .propose)
    (h : RecvEndO kk c id s m s') : RoOk s' := by
  rcases h with ⟨-, hh⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact roOk_handle hs hsc hh
  · exact hs
  · refine roOk_handle ?_ hsc hh
    rcases hpre with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨hs.1, fun h => by simp [pbecomeFollower] at h⟩
    · exact hs

theorem roOk_tick {c : CfgM} {id : w64} {s s' : PState} (hs : RoOk s) (h : TickEndO kk c id s s') :
    RoOk s' := by
  rcases h with rfl | ⟨-, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
  · exact hs
  · exact ⟨hs.1, fun h => by simp [psendMsgs, pbecomeCandidate] at h⟩
  · exact hs

theorem roOk_adv {c : CfgM} {id : w64} {s s' : PState} {qs : List Msg} (hs : RoOk s)
    (hq : ∀ q ∈ qs, q.ty = .appResp ∨ q.ty = .voteResp) (h : AdvanceEndO kk c id s qs s') :
    RoOk s' := by
  induction h with
  | nil => exact hs
  | cons s s1 s' q qs hr _ ih =>
    refine ih ?_ (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    refine roOk_recv hs ?_ hr
    rcases hq q (List.mem_cons_self ..) with h | h <;> simp [h]

/-- **A leader has no read request pending along `Reach`** (`NodeFacts.roPend` at the state a
`Ready` is taken at). -/
theorem reach_roOk {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hnet : NetOk R S net) (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    RoOk r₁.p := by
  obtain ⟨hmd, _, _, _, _, _, _, hty⟩ := hin.b1a hmsk
  have hs : RoOk v.ps := ⟨hv.facts.pend0 (by rw [hmd]), hv.facts.roPend (by rw [hmd])⟩
  cases hr with
  | stay _ => exact hs
  | input inp _ hinp _ _ _ _ hm _ hst =>
    rcases Input.step_b1a hmsk hin hinp hst with ⟨m, rfl⟩ | ⟨-, hst⟩ | ⟨d, rfl⟩
    · obtain ⟨hmn, -, -⟩ := hm m rfl
      exact roOk_recv hs (ty7_of_s4 (hty m hmn)) (RecvEnd.toO_in hmsk hin hnet hv hmn hst.1)
    · exact roOk_tick hs (TickEnd.toO_in hmsk hin hst.1)
    · rcases (RecvEnd.toO_prop hmsk hin hv hst.1) with ⟨-, hh⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact roOk_propose hh hs
      · exact absurd rfl h0
      · exact absurd rfl h0
  | advance _ _ _ _ _ _ ha _ =>
    exact roOk_adv hs (fun q hq => ((hv.qs q hq).2.2.2.2).imp (fun h => h.1) (fun h => h.1))
      (advanceEndR_toO hmsk hin hv ha)

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
theorem reach_keep {msk : SimMask} (hmsk : msk ≤ mskB1a) {R : RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg} {xnet : List XMsg}
    {n : Fin R.N} {v : NodeView} {r₁ : RState} (hin : InMask msk R net xnet)
    (hv : NodeOk R dec S net n v) (hr : ReachIn msk R dec Adm net xnet n v r₁) :
    (r₁.cfg = v.r.cfg ∧ r₁.fp = v.r.fp ∧ r₁.snap = v.r.snap) ∧ v.pend = [] ∧ v.xpend = [] := by
  obtain ⟨hmd, _, _, _, _, _, _, hty⟩ := hin.b1a hmsk
  cases hr with
  | stay hi => exact ⟨⟨rfl, rfl, rfl⟩, hi.2.1, hi.2.2.1⟩
  | input inp _ hinp hi _ _ _ hm _ hst =>
    refine ⟨?_, hi.2.1, hi.2.2.1⟩
    rcases Input.step_b1a hmsk hin hinp hst with ⟨m, rfl⟩ | ⟨-, hst⟩ | ⟨d, rfl⟩
    · obtain ⟨hmn, -, -⟩ := hm m rfl
      exact recvEndR_keep hst
        (by rcases hty m hmn with h | h | h | h | h | h | h <;> rw [h] <;> decide)
    · exact ⟨hst.2.1.2.2, hst.2.2.1, hst.2.2.2.1⟩
    · exact recvEndR_keep hst (by simp [propMsg])
  | advance _ hp hxp _ _ _ _ hns =>
    refine ⟨advanceNoSnap_keep (hns (by rw [hmd])) fun q hq => ?_, hp, hxp⟩
    rcases ((hv.qs q hq).2.2.2.2).imp (fun h => h.1) (fun h => h.1) with h | h <;> rw [h] <;> decide

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
