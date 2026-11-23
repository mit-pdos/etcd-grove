/-
Lean-first (no Rocq counterpart). #33 S3b W5 (2026-11-23): laws for the proofs of `Boot` and `Send`
(`State__Boot.lean`, `State__Send.lean`): `Boot`'s tail (after the restore) as a function of the
state it starts from, the restored log within budget, and a log field read from an owned successor.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.BootSendLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

set_option linter.unusedSimpArgs false

/-- `Boot`'s tail (B 182-194, after the restore), from the state `ns` the restore left. -/
def bootSendP_bootTail (s ns : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let mut ns := ns
  let a ← if ev.applied.isSome then need ev.applied else pure 0
  let logn := ns.log[n]!
  if !(← orM (pure (a == 0))
        (andM (pure (decide (a ≤ logn.length) && decide (a ≤ s.chain.length)))
          (do entriesEqual (← subSeq s.chain 1 a) (← subSeq logn 1 a)))) then
    return none
  ns := { ns with lastApplied := s.lastApplied.set n a }
  let c ← confOf logn a s.initConf
  ns := { ns with config := s.config.set n c }
  ns := { ns with confAt := s.confAt.set n (← lastConf logn a) }
  if !(← sameConf ev c) then return none
  return some ns

/-- `Boot`'s tail after the applied index `a`. -/
def bootSendP_bootRest (s ns : State) (n : Nat) (ev : Event) (a : Int) : EvalM (Option State) := do
  let mut ns := ns
  let logn := ns.log[n]!
  if !(← orM (pure (a == 0))
        (andM (pure (decide (a ≤ logn.length) && decide (a ≤ s.chain.length)))
          (do entriesEqual (← subSeq s.chain 1 a) (← subSeq logn 1 a)))) then
    return none
  ns := { ns with lastApplied := s.lastApplied.set n a }
  let c ← confOf logn a s.initConf
  ns := { ns with config := s.config.set n c }
  ns := { ns with confAt := s.confAt.set n (← lastConf logn a) }
  if !(← sameConf ev c) then return none
  return some ns

/-- `Boot`'s tail: the applied index, then the rest. -/
theorem bootSendP_bootTail_ok {s ns : State} {n : Nat} {ev : Event} {o : Option State}
    (h : bootSendP_bootTail s ns n ev = .ok o) :
    ∃ a, (if ev.applied.isSome then need ev.applied else pure 0 : EvalM Int) = .ok a ∧
      bootSendP_bootRest s ns n ev a = .ok o := by
  unfold bootSendP_bootTail at h
  by_cases hap : ev.applied.isSome = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hap)] at h ⊢
    obtain ⟨a, ha, h⟩ := bind_ok h
    exact ⟨a, ha, h⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hap)] at h ⊢
    obtain ⟨a, ha, h⟩ := bind_ok h
    exact ⟨a, ha, h⟩

theorem bootSendP_w64_eq_zero {u : w64} : u = W64 0 ↔ sint.Z u = 0 := by
  constructor
  · intro h; subst h; rfl
  · intro h; word

theorem bootSendP_w64_eq {u v : w64} : u = v ↔ sint.Z u = sint.Z v := by
  constructor
  · intro h; subst h; rfl
  · intro h; word

/-- `ConfOf(l, a, s.InitConf())`'s premise, for a log within budget. -/
theorem bootSendP_confOf_bounded {s : State} {l : List Entry} {b E w : Nat} (hl : logWithin b E l)
    (hE : ((s.cfg.initVoters.length + (b + w + 1) * E : Nat) : Int) < 2 ^ 61) :
    ConfOf.Bounded l s.initConf := by
  unfold ConfOf.Bounded State.initConf Config.initConf
  have h := logWithin_chgSum hl
  have : b * E ≤ (b + w + 1) * E := Nat.mul_le_mul_right _ (by omega)
  simp only [List.length_nil, Nat.add_zero]
  omega

/-- The restored log `SubSeq(s.Log[n], 1, u.Keep) ++ u.Suffix` within budget. -/
theorem bootSendP_restored_log {s : State} {b E n : Nat} {u : Pre} {pre : List Entry}
    (hW : s.Within b E) (hu : s.undo[n]! = some u) (hpre : subSeq (s.log[n]!) 1 u.keep = .ok pre) :
    logWithin b E (pre ++ u.suffix) := by
  have hlog0 : logWithin b E (s.log[n]!) :=
    getElem!_mem' (α := List Entry) (P := fun l => logWithin b E l) hW.log ⟨Nat.zero_le _, fun x hx => by cases hx⟩
  have huw : u.Within b E := hW.undo _ (getElem!_some_mem hu) u rfl
  obtain ⟨-, -, -, -, -, -, -, hu8, hu9, -⟩ := huw
  have hpl := bootSend_subSeq_one_length hpre
  refine ⟨?_, fun e he => ?_⟩
  · simp only [List.length_append]
    have := hu8.1
    omega
  · rcases List.mem_append.1 he with he | he
    · exact hlog0.2 e (bootSend_subSeq_mem hpre he)
    · exact hu8.2 e he

/-! ## `Send` -/

/-- `Send`'s `mine` (B 516-519): the write's facts, for a boot report. -/
def bootSendP_mine (bt : Bool) (o : Option Pre) : List Fact :=
  match bt, o with
  | true, some u => u.msgs
  | _, _ => []

/-- `Send`'s `cast` (B 516-519): the write's votes, for a boot report. -/
def bootSendP_cast (bt : Bool) (o : Option Pre) : List VoteRec :=
  match bt, o with
  | true, some u => u.votes
  | _, _ => []

/-- `Send`'s `dur` (B 520): no write pending, or it was made durable. -/
def bootSendP_dur (o : Option Pre) : Bool :=
  match o with
  | none => true
  | some u => u.made

/-- `Send`'s tail (B 524-593, after the sender's checks and the write's clearing). -/
def bootSendP_sendTail (s ns : State) (n : Nat) (ev : Event) (m : Msg) (me : Str) (late bt dur : Bool)
    (mine : List Fact) (cast : List VoteRec) : EvalM (Option State) := do
  let mut ns := ns
  let t ← m.typ
  if t == go!"vote" then
    if bt then
      if !(← andM (pure dur) (orM (do pure (s.msgs.contains (← voteFact m)))
            (do pure (mine.contains (← voteFact m))))) then return none
    else if !(← andM (do pure ((← m.term_) == s.currentTerm[n]!))
          (do pure (s.msgs.contains (← voteFact m)))) then return none
    return some ns
  if t == go!"voteresp" then
    if !(← m.reject_) then
      let v : VoteRec := { voter := me, term := ← m.term_, cand := ← m.to_ }
      if !(s.votes.contains v || cast.contains v) then return none
      if bt && !dur then return none
      ns := { ns with msgs := lset.add s.msgs { type := go!"grant", src := me, dst := ← m.to_, term := ← m.term_ } }
    return some ns
  if (← isReq m) then
    if !(← orM (pure bt) <| andM (do pure ((← m.term_) == s.currentTerm[n]!))
          (pure (s.role[n]! == leader))) then return none
    if !(← andM (snapOk s.ledLog m) (do s.sendable (← reqFactIn s.ledLog m))) then return none
    return some ns
  if t == go!"appresp" then
    if (← m.reject_) then return some ns
    if bt then
      if (← m.index_) == 0 then return some ns
      let ok ← match s.undo[n]! with
        | none => pure false
        | some u => andM (pure dur) (do pure (u.acks.contains (ackFact me (← m.to_) (← m.term_) (← m.index_))))
      if !ok then return none
      return some ns
    let c ← if late then need ev.cause else pure (s.pending[n]!)
    if (← andM (pure (c != [])) <| andM (isReq (c[0]!))
          (do pure (decide ((← (c[0]!).term_) < s.currentTerm[n]!)))) then
      if !(← andM (do pure ((← m.index_) == 0)) (do pure ((← m.term_) == s.currentTerm[n]!))) then
        return none
      return some ns
    if (← m.index_) == 0 then return some ns
    if c == [] then return none
    let cm ← msgSeqHead c
    let f ← reqFactIn s.ledLog cm
    let last := f.prevLogIndex + f.entries.length
    if !(← andM (orM (do pure ((← cm.typ) == go!"app")) (do pure ((← cm.typ) == go!"snap"))) <|
          andM (snapOk s.ledLog cm) (s.sendable f)) then return none
    if !(← andM (do pure ((← m.to_) == (← cm.from_))) <| andM (do pure ((← m.term_) == (← cm.term_)))
          (do pure (s.currentTerm[n]! == (← cm.term_)))) then return none
    if (← andM (do pure ((← m.index_) == last)) <| andM (s.prevOk n f) (s.hasFirst n f f.entries.length)) then
      let old := s.confirmed[n]!
      let ct ← cm.term_
      let idx := if old.term == ct then imax old.index last else last
      ns := { ns with msgs := lset.add s.msgs (ackFact me (← cm.from_) ct last),
                      confirmed := s.confirmed.set n { term := ct, index := idx } }
      return some ns
    if !(← andM (pure (decide (f.prevLogIndex < s.commitIndex[n]!)))
          (do pure ((← m.index_) == s.commitIndex[n]!))) then return none
    ns := { ns with msgs := lset.add s.msgs (ackFact me (← cm.from_) (← cm.term_) (s.commitIndex[n]!)) }
    return some ns
  if t == go!"hbresp" then
    let t' := if bt then s.effTerm n else s.currentTerm[n]!
    if !decide (t' ≤ (← m.term_)) then return none
    return some ns
  if isUnmodelled t then return some ns
  return none

/-- `Send` taken apart: the message, the sender's checks, then the tail from the state with the write
cleared (or not). -/
theorem bootSendP_send_ok {s : State} {n : Nat} {ev : Event} {o : Option State}
    (h : State.send s n ev = .ok o) :
    ∃ m, need ev.msg = .ok m ∧
      ∃ x1, orM (do pure ((← m.from_) == s.cfg.server[n]!)) (do pure (isForwarded (← m.typ))) = .ok x1 ∧
        (x1 = false → o = none) ∧ (x1 = true →
      ∃ x2, andM (do pure (s.cfg.server.has (← m.to_))) (do pure ((← m.to_) != s.cfg.server[n]!)) = .ok x2 ∧
        (x2 = false → o = none) ∧ (x2 = true →
      bootSendP_sendTail s (if !(ev.cause.isSome || ev.b) then { s with undo := s.undo.set n none } else s) n ev m
        (s.cfg.server[n]!) ev.cause.isSome ev.b (bootSendP_dur (s.undo[n]!)) (bootSendP_mine ev.b (s.undo[n]!))
        (bootSendP_cast ev.b (s.undo[n]!)) = .ok o)) := by
  unfold State.send at h
  obtain ⟨m, hm, h⟩ := bind_ok h
  refine ⟨m, hm, ?_⟩
  obtain ⟨x1, hx1, h⟩ := bind_ok h
  refine ⟨x1, hx1, fun h1 => ?_, fun h1 => ?_⟩
  · subst h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at h; cases h; rfl
  subst h1
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at h
  obtain ⟨x2, hx2, h⟩ := bind_ok h
  refine ⟨x2, hx2, fun h2 => ?_, fun h2 => ?_⟩
  · subst h2
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at h; cases h; rfl
  subst h2
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at h
  unfold bootSendP_sendTail bootSendP_dur bootSendP_mine bootSendP_cast
  generalize ev.b = bt at h ⊢
  generalize s.undo[n]! = uo at h ⊢
  by_cases hlb : (!(ev.cause.isSome || bt)) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hlb)] at h ⊢
    cases bt <;> cases uo <;> exact h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hlb)] at h ⊢
    cases bt <;> cases uo <;> exact h

/-- `Send`'s `c := ev.cause() or s.Pending[n]` (B 557) taken apart from the rest of the appresp tail. -/
theorem bootSendP_cjoin_ok {β : Type} {late : Bool} {x : Option (List Msg)} {P : List Msg}
    {f : List Msg → EvalM β} {o : β}
    (h : (if late = true then (do let c ← need x; f c) else (do let c ← pure P; f c)) = .ok o) :
    ∃ c, (if late = true then need x else pure P : EvalM (List Msg)) = .ok c ∧ f c = .ok o := by
  cases late
  · exact bind_ok h
  · exact bind_ok h

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- An owned successor's struct opened to read its `Log` field. -/
theorem bootSendP_stateOwn_log (q : Loc) (s : State) :
    stateOwn (GF := GF) q s ⊢ ∃ g : G.State, q ↦ g ∗ logsRO g.Log' s.log ∗ ⌜s.Wf⌝ ∗ (q ↦ g -∗ stateOwn q s) := by
  iintro Hq
  iunfold stateOwn at Hq
  iNamed Hq
  icases Hf with #Hf
  ihave #Hf2 := Hf
  iNamed Hf2
  iexists g
  iframe Hp HLog
  isplitr
  · ipureintro; exact HWf
  iintro Hp
  iunfold stateOwn
  iexists g
  iframe Hp Hf

/-- `c[k]` of a `[]Msg`. -/
theorem bootSendP_msgsRO_at (sl : GoSlice) (ms : List Msg) (k : w64) (hk : 0 ≤ sint.Z k ∧ sint.Z k < ms.length) :
    msgsRO (GF := GF) sl ms ⊢ ∃ g : G.Msg, sliceAt sl k g ∗ msgRO g ms[sint.nat k]! := by
  iintro #H
  iunfold msgsRO at H
  icases H with ⟨%gs, #Hgs, #Hb⟩
  iapply sliceRO_at (fun g m => msgRO (GF := GF) g m) sl gs ms k hk
  iframe Hgs Hb

/-- `c[0]` of a nonempty `[]Msg`. -/
theorem bootSendP_msgsRO_head (sl : GoSlice) (ms : List Msg) (h : ms ≠ []) :
    msgsRO (GF := GF) sl ms ⊢ ∃ g : G.Msg, sliceAt sl (W64 0) g ∗ msgRO g ms[0]! := by
  have hl : 0 < ms.length := List.length_pos_iff.2 h
  have := bootSendP_msgsRO_at (GF := GF) sl ms (W64 0) ⟨by decide, by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩
  exact this

end iris

end AntCheck
end EtcdGrove
end Perennial
