/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): no action writes `cfg`: the twelve
actions `Within/StepCfg.lean` takes as hypotheses keep it (`State.<act>_cfg`), and the plain law
`State.step_cfg` (`Step`'s successor has its state's configuration).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.StepCfg
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws2

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem actionCfg_none {x : State} (h : (pure none : EvalM (Option State)) = .ok (some x)) : False := by
  cases h

theorem actionCfg_some {s x y : State} (h : (pure (some y) : EvalM (Option State)) = .ok (some x))
    (hy : y.cfg = s.cfg) : x.cfg = s.cfg := by
  cases h; exact hy

theorem actionCfg_ite {α : Type} {c : Prop} [Decidable c] {a b : EvalM α} {r : α}
    (h : (if c then a else b) = .ok r) : a = .ok r ∨ b = .ok r := by
  by_cases hc : c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact .inl h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; exact .inr h

-- Peel an action's `do`-block at `ho : act = .ok (some s')` down to its `return`s: every
-- successor is `s` with fields other than `cfg` updated.
set_option hygiene false in
local macro "cfg_peel" : tactic => `(tactic|
  repeat' (first
    | (dsimp only at ho)
    | (split at ho)
    | (with_reducible obtain ⟨_, -, ho⟩ := bind_ok ho)
    | (with_reducible exact (actionCfg_none ho).elim)
    | (with_reducible exact actionCfg_some ho (by first | rfl | assumption))
    | (with_reducible rcases actionCfg_ite ho with ho | ho)))

theorem State.made_cfg : W6Laws.KeepsCfg State.made := by
  intro s n ev s' ho; unfold State.made at ho; cfg_peel

theorem State.wrote_cfg : W6Laws.KeepsCfg State.wrote := by
  intro s n ev s' ho; unfold State.wrote at ho; cfg_peel

theorem State.recv_cfg : W6Laws.KeepsCfg State.recv := by
  intro s n ev s' ho; unfold State.recv at ho; cfg_peel

theorem State.net_cfg : W6Laws.KeepsCfg State.net := by
  intro s n ev s' ho; unfold State.net at ho; cfg_peel

theorem State.applyEv_cfg : W6Laws.KeepsCfg State.applyEv := by
  intro s n ev s' ho; unfold State.applyEv at ho; cfg_peel

theorem State.restoreEv_cfg : W6Laws.KeepsCfg State.restoreEv := by
  intro s n ev s' ho; unfold State.restoreEv at ho; cfg_peel

theorem State.confEv_cfg : W6Laws.KeepsCfg State.confEv := by
  intro s n ev s' ho; unfold State.confEv at ho; cfg_peel

theorem State.snapEv_cfg : W6Laws.KeepsCfg State.snapEv := by
  intro s n ev s' ho; unfold State.snapEv at ho; cfg_peel

theorem State.readAsked_cfg : W6Laws.KeepsCfg State.readAsked := by
  intro s n ev s' ho; unfold State.readAsked at ho; cfg_peel

theorem State.readGiven_cfg : W6Laws.KeepsCfg State.readGiven := by
  intro s n ev s' ho; unfold State.readGiven at ho; cfg_peel

theorem State.boot_cfg : W6Laws.KeepsCfg State.boot := by
  intro s n ev s' ho; unfold State.boot at ho; cfg_peel

/-- `Send`'s tail (B 529-593, after the sender checks), over any `ns` with `s`'s configuration. -/
theorem actionCfg_send_tail {s ns s' : State} {n : Nat} {ev : Event} {m : Msg} {me : Str}
    {late bt dur : Bool} {mine : List Fact} {cast : List VoteRec} (hcfg : ns.cfg = s.cfg)
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
    s'.cfg = s.cfg := by
  repeat' (first
    | exact (actionCfg_none ho).elim
    | (exact actionCfg_some ho (by first | rfl | exact hcfg))
    | (have h' := bind_ok ho; clear ho; obtain ⟨_, _, ho⟩ := h')
    | (have h' := actionCfg_ite ho; clear ho; rcases h' with ho | ho)
    | (split at ho))

theorem State.send_cfg : W6Laws.KeepsCfg State.send := by
  intro s n ev s' ho
  unfold State.send at ho
  obtain ⟨m, -, ho⟩ := bind_ok ho
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
    exact actionCfg_send_tail (ns := { s with undo := s.undo.set n none }) rfl ho
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hlb)] at ho
    exact actionCfg_send_tail (ns := s) rfl ho

/-- **`Step`'s successor has its state's configuration** (W7's `CheckLaws.StepCfg`). -/
theorem State.step_cfg : ∀ (s : State) (ev : Event) (s' : State), s.step ev = .ok (some s') → s'.cfg = s.cfg :=
  State.step_cfg_of State.onDisk_keeps State.boot_cfg State.recv_cfg State.wrote_cfg State.net_cfg
    State.made_cfg State.send_cfg State.applyEv_cfg State.restoreEv_cfg State.confEv_cfg State.snapEv_cfg
    State.readAsked_cfg State.readGiven_cfg

end AntCheck
end EtcdGrove
end Perennial
