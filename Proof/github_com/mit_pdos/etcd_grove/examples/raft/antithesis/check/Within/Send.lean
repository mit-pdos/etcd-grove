/-
Lean-first (no Rocq counterpart). #33 S3b W5 (2026-11-23): the budget law of `Send` (`State.send_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.BootSendLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem bootSend_ite_ok {α : Type} {c : Prop} [Decidable c] {a b : EvalM α} {r : α}
    (h : (if c then a else b) = .ok r) : (c ∧ a = .ok r) ∨ (¬c ∧ b = .ok r) := by
  by_cases hc : c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact .inl ⟨hc, h⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; exact .inr ⟨hc, h⟩

theorem bootSend_none_ne {α : Type} {x : α} (h : (pure none : EvalM (Option α)) = .ok (some x)) : False := by
  cases h

theorem bootSend_some_eq {α : Type} {x y : α} (h : (pure (some y) : EvalM (Option α)) = .ok (some x)) : x = y := by
  cases h; rfl

theorem bootSend_le_sum_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y t ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with h | h
    · omega
    · have := ih h; omega

/-! ### `Send`'s new facts within budget -/

theorem bootSend_within_msgsAdd' {ns : State} {b E : Nat} {M : List Fact} {f : Fact} (hns : ns.Within b E)
    (hM : M = ns.msgs) (hf : f.NumsOk) : ({ ns with msgs := lset.add M f } : State).Within (b + 1) E := by
  subst hM; exact bootSend_within_msgsAdd hns hf

theorem bootSend_within_msgsAddConf' {ns : State} {b E n : Nat} {M : List Fact} {C : List Confirmed} {f : Fact}
    {c : Confirmed} (hns : ns.Within b E) (hM : M = ns.msgs) (hC : C = ns.confirmed) (hf : f.NumsOk)
    (hc : bigOk c.term ∧ bigOk c.index) :
    ({ ns with msgs := lset.add M f, confirmed := C.set n c } : State).Within (b + 1) E := by
  subst hM hC; exact bootSend_within_confirmedSet (bootSend_within_msgsAdd hns hf) hc

theorem bootSend_grant_ok {ty a d : Str} {t : Int} (h : bigOk t) :
    Fact.NumsOk { type := ty, src := a, dst := d, term := t } := by
  unfold Fact.NumsOk; dsimp only
  exact ⟨h, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

theorem bootSend_ackFact_ok {a d : Str} {t k : Int} (ht : bigOk t) (hk : bigOk k) : (ackFact a d t k).NumsOk := by
  unfold Fact.NumsOk ackFact; dsimp only
  exact ⟨ht, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, hk⟩

theorem bootSend_term_bigOk {m : Msg} {t : Int} (hN : m.NumsOk) (h : m.term_ = .ok t) : bigOk t := by
  have := hN.1; unfold Msg.term_ at h; rw [need_ok h] at this; exact bigOk_of_numOk this

theorem bootSend_c_cause {ev : Event} {b : Nat} {c : List Msg}
    (hcause : ∀ ms, ev.cause = some ms → ∀ x ∈ ms, x.NumsOk ∧ x.size ≤ b + ev.weight)
    (h : need ev.cause = .ok c) : ∀ x ∈ c, x.NumsOk ∧ x.size ≤ b + ev.weight :=
  hcause c (need_ok h)

theorem bootSend_c_pending {s : State} {n b E : Nat} {ev : Event} {c : List Msg} (hW : s.Within b E)
    (h : (pure (s.pending[n]!) : EvalM (List Msg)) = .ok c) : ∀ x ∈ c, x.NumsOk ∧ x.size ≤ b + ev.weight := by
  cases h
  have hp := getElem!_mem' (α := List Msg) (P := fun ms => ms.length ≤ b ∧ ∀ m ∈ ms, m.Within b E) hW.pending
    ⟨Nat.zero_le _, fun m hm => by cases hm⟩ (n := n)
  intro x hx
  have := hp.2 x hx
  exact ⟨this.1, by have := this.2.1; omega⟩

theorem bootSend_cm {P : Msg → Prop} {c : List Msg} {cm : Msg} (hc : ∀ x ∈ c, P x) (h : msgSeqHead c = .ok cm) :
    P cm := hc cm (msgSeqHead_mem h)

theorem bootSend_last_bigOk {s : State} {b E : Nat} {ev : Event} {cm : Msg} {f : AppendFact}
    (hcm : cm.NumsOk ∧ cm.size ≤ b + ev.weight) (hW : s.Within b E) (hb : ((b + ev.weight : Nat) : Int) < 2 ^ 61)
    (h : reqFactIn s.ledLog cm = .ok f) : bigOk (f.prevLogIndex + f.entries.length) := by
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  obtain ⟨h1, h2, -⟩ := reqFactIn_within hcm hW'.ledLog h
  unfold numOk numBound at h1; unfold bigOk; omega

theorem bootSend_idx_bigOk {c : Prop} [Decidable c] {x y : Int} (hx : bigOk x) (hy : bigOk y) :
    bigOk (if c then imax x y else y) := by
  split
  · unfold imax; split <;> assumption
  · exact hy

theorem bootSend_confirmed_bigOk {s : State} {b E n : Nat} (hW : s.Within b E) : bigOk (s.confirmed[n]!).index :=
  (getElem!_mem' (α := Confirmed) (P := fun c => bigOk c.term ∧ bigOk c.index) hW.confirmed
    ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩).2

theorem bootSend_commit_bigOk {s : State} {b E n : Nat} (hW : s.Within b E) : bigOk (s.commitIndex[n]!) :=
  getElem!_mem' (α := Int) (P := bigOk) hW.commitIndex ⟨by decide, by decide⟩

/-- `Send`'s tail (B 524-593, after the sender's checks and the write's clearing), over the state
`ns` it returns or adds one fact to. -/
theorem bootSend_send_tail {s ns s' : State} {n : Nat} {ev : Event} {b E : Nat} {m : Msg} {me : Str}
    {late bt dur : Bool} {mine : List Fact} {cast : List VoteRec}
    (hW : s.Within b E) (hb : ((b + ev.weight : Nat) : Int) < 2 ^ 61)
    (hns : ns.Within b E) (hmsgs : ns.msgs = s.msgs) (hconf : ns.confirmed = s.confirmed) (hmN : m.NumsOk)
    (hcause : ∀ ms, ev.cause = some ms → ∀ c ∈ ms, c.NumsOk ∧ c.size ≤ b + ev.weight)
    (ho : (do
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
      : EvalM (Option State)) = .ok (some s')) :
    s'.Within (b + 1) E := by
  repeat' (first
    | exact (bootSend_none_ne ho).elim
    | (obtain rfl := bootSend_some_eq ho)
    | (have h' := bind_ok ho; clear ho; obtain ⟨_, _, ho⟩ := h')
    | (have h' := bootSend_ite_ok ho; clear ho; rcases h' with ⟨_, ho⟩ | ⟨_, ho⟩)
    | (split at ho))
  all_goals first
    | exact State.Within.mono' (by omega) (Nat.le_refl _) hns
    | (refine bootSend_within_msgsAdd' hns hmsgs.symm (bootSend_grant_ok ?_)
       exact bootSend_term_bigOk hmN (by assumption))
    | (refine bootSend_within_msgsAddConf' hns hmsgs.symm hconf.symm (bootSend_ackFact_ok ?_ ?_) ⟨?_, ?_⟩)
    | (refine bootSend_within_msgsAdd' hns hmsgs.symm (bootSend_ackFact_ok ?_ ?_))
  all_goals try dsimp only
  all_goals first
    | exact bootSend_commit_bigOk hW
    | (refine bootSend_idx_bigOk (bootSend_confirmed_bigOk hW) ?_)
    | skip
  all_goals first
    | exact bootSend_commit_bigOk hW
    | (have hc := bootSend_c_cause hcause (by assumption)
       have hcm := bootSend_cm hc (by assumption)
       first
       | exact bootSend_term_bigOk hcm.1 (by assumption)
       | exact bootSend_last_bigOk hcm hW hb (by assumption))
    | (have hc := bootSend_c_pending (ev := ev) (n := n) hW (by assumption)
       have hcm := bootSend_cm hc (by assumption)
       first
       | exact bootSend_term_bigOk hcm.1 (by assumption)
       | exact bootSend_last_bigOk hcm hW hb (by assumption))


theorem State.send_within : ActionWithin State.send := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.send at ho
  obtain ⟨m, hm, ho⟩ := bind_ok ho
  have hmN : m.NumsOk := hNO.2.2.2.2.2.2.2.2.2.2.2.1 m (need_ok hm)
  have hcause : ∀ ms, ev.cause = some ms → ∀ c ∈ ms, c.NumsOk ∧ c.size ≤ b + ev.weight := by
    intro ms hms c hc
    refine ⟨hNO.2.2.2.2.2.2.2.2.2.2.2.2 ms hms c hc, ?_⟩
    have h1 : c.size ≤ ((ev.cause.getD []).map Msg.size).sum := by
      rw [hms]; exact bootSend_le_sum_of_mem (List.mem_map_of_mem hc)
    unfold Event.weight Event.size; omega
  suffices H : s'.Within (b + 1) E from State.Within.mono' (by omega) (Nat.le_refl _) H
  obtain ⟨o1, -, ho⟩ := bind_ok ho
  cases o1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at ho; cases ho
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at ho
  obtain ⟨o2, -, ho⟩ := bind_ok ho
  cases o2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at ho; cases ho
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at ho
  by_cases hlb : (!(ev.cause.isSome || ev.b)) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hlb)] at ho
    exact bootSend_send_tail (ns := { s with undo := s.undo.set n none }) hW hb (bootSend_within_undoNone hW) rfl rfl hmN hcause ho
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hlb)] at ho
    exact bootSend_send_tail (ns := s) hW hb hW rfl rfl hmN hcause ho
  done

end AntCheck
end EtcdGrove
end Perennial
