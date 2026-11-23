/-
Lean-first (no Rocq counterpart). #33 S3b W5 (2026-11-23): the budget law of `Boot` (`State.boot_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.BootSendLaws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

/-- `Boot`'s tail (B 182-194, after the restore): the applied index, the configuration and its
index set from the log `ns` holds. -/
theorem bootSend_boot_tail {s ns s' : State} {n : Nat} {ev : Event} {b E : Nat}
    (hW : s.Within b E) (hNO : ev.NumsOk) (hb : ((b + ev.weight : Nat) : Int) < 2 ^ 61)
    (hns : ns.Within (b + ev.weight) E) (hcfg : ns.cfg = s.cfg) (hlog : logWithin b E (ns.log[n]!))
    (ho : (do
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
      return some ns : EvalM (Option State)) = .ok (some s')) :
    s'.Within (b + ev.weight) E := by
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  dsimp only at ho
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  split at ho <;> obtain ⟨a, ha, ho⟩ := bind_ok ho
  all_goals have han : numOk a := (by first | (have := hNO.2.2.2.2.2.1; rw [need_ok ha] at this; exact this) | (cases ha; unfold numOk numBound; omega))
  all_goals clear ha
  all_goals
    obtain ⟨ok1, hok1, ho⟩ := bind_ok ho
    split at ho
    · cases ho
    rename_i hok1t
    have hok1t' : ok1 = true := by simpa using hok1t
    subst hok1t'
    have hab : a.toNat ≤ b := by
      obtain ⟨x, hx, _, hx2⟩ := orM_ok hok1
      cases hx
      by_cases hz : a = 0
      · omega
      · have hz' : (a == 0) = false := by simpa using hz
        obtain ⟨y, hy, hy1, hy2⟩ := andM_ok (hx2 hz')
        cases hy
        by_cases hy' : (decide (a ≤ ↑(ns.log[n]!).length) && decide (a ≤ ↑s.chain.length)) = true
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hy'; have := hlog.1; omega
        · simp only [Bool.not_eq_true] at hy'; exact absurd (hy2 hy') (by simp)
    obtain ⟨c, hc, ho⟩ := bind_ok ho
    obtain ⟨lc, hlc, ho⟩ := bind_ok ho
    obtain ⟨sc, -, ho⟩ := bind_ok ho
    split at ho
    · cases ho
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    have hlcb := bootSend_lastConf_bounds hlc
    have hcb := bootSend_confOf_length (K := s.cfg.initVoters.length) (fun e he => (hlog.2 e he).2)
      (by unfold State.initConf Config.initConf; simp) hc
    have hm : a.toNat * E ≤ (b + ev.weight) * E := Nat.mul_le_mul_right _ (by omega)
    have hcw : confWithin s.cfg.initVoters.length (b + ev.weight) E c := by
      unfold confWithin; constructor <;> omega
    refine ⟨hns.cfg, hns.i_pos, hns.i_le, hns.currentTerm, hns.voteTerm, hns.commitIndex, ?_, ?_, hns.confirmed, hns.log, hns.chain, hns.ledLog_len, hns.ledLog, ?_, hns.ledConf_len, hns.ledConf, hns.ledAt, hns.elAt, hns.termLen, hns.msgs_len, hns.msgs, hns.votes_len, hns.votes, hns.leaders_len, hns.leaders, hns.undo, hns.pending, hns.queue, hns.reads, hns.viol⟩
    · exact forall_mem_set hW'.lastApplied (bigOk_of_numOk han)
    · refine forall_mem_set hW'.confAt ?_
      unfold bigOk; omega
    · show ∀ x ∈ s.config.set n c, confWithin ns.cfg.initVoters.length (b + ev.weight) E x
      rw [hcfg]; exact forall_mem_set hW'.config hcw


theorem State.boot_within : ActionWithin State.boot := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  have hlog0 : logWithin b E (s.log[n]!) :=
    getElem!_mem' (α := List Entry) (P := fun l => logWithin b E l) hW.log ⟨Nat.zero_le _, fun x hx => by cases hx⟩
  -- the cleared state: no write, nothing pending, queued or read, a follower
  have hns0 : ({ s with undo := s.undo.set n none, pending := s.pending.set n [],
                        queue := s.queue.set n [], reads := s.reads.set n [],
                        role := s.role.set n follower } : State).Within (b + ev.weight) E :=
    ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, hW'.lastApplied, hW'.confAt, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, hW'.config, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders,
      forall_mem_set hW'.undo (fun u hu => by cases hu),
      forall_mem_set hW'.pending ⟨Nat.zero_le _, fun m hm => by cases hm⟩,
      forall_mem_set hW'.queue ⟨Nat.zero_le _, fun it hit => by cases hit⟩,
      forall_mem_set hW'.reads ⟨Nat.zero_le _, fun x hx => by cases hx⟩, hW'.viol⟩
  unfold State.boot at ho
  obtain ⟨r, -, ho⟩ := bind_ok ho
  dsimp only at ho
  split at ho
  · -- the write restored
    split at ho
    · cases ho
    rename_i u hu
    split at ho
    · cases ho
    obtain ⟨pre, hpre, ho⟩ := bind_ok ho
    obtain ⟨r2, -, ho⟩ := bind_ok ho
    split at ho
    · cases ho
    have huw : u.Within b E := hW.undo _ (getElem!_some_mem hu) u rfl
    obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, hu10, hu11, hu12, hu13, hu14, hu15⟩ := huw
    have hpl := bootSend_subSeq_one_length hpre
    have hlog : logWithin b E (pre ++ u.suffix) := by
      refine ⟨?_, fun e he => ?_⟩
      · simp only [List.length_append]
        have := hu8.1
        omega
      · rcases List.mem_append.1 he with he | he
        · exact hlog0.2 e (bootSend_subSeq_mem hpre he)
        · exact hu8.2 e he
    have hlog' := hlog.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _)
    refine bootSend_boot_tail (ns := { s with undo := (s.undo.set n none), pending := (s.pending.set n []), queue := (s.queue.set n []), reads := (s.reads.set n []), role := (s.role.set n follower), currentTerm := (s.currentTerm.set n u.term), voteTerm := (s.voteTerm.set n u.voteTerm), voteFor := (s.voteFor.set n u.voteFor), commitIndex := (s.commitIndex.set n u.commit), log := (s.log.set n (pre ++ u.suffix)), confirmed := (s.confirmed.set n u.confirmed), msgs := (lset.minus s.msgs u.msgs), votes := (lset.minus s.votes u.votes) }) hW hNO hb ?_ rfl ?_ (by dsimp only; exact ho)
    · refine ⟨hns0.cfg, hns0.i_pos, hns0.i_le, forall_mem_set hW'.currentTerm hu1, forall_mem_set hW'.voteTerm hu2,
        forall_mem_set hW'.commitIndex hu3, hns0.lastApplied, hns0.confAt, forall_mem_set hW'.confirmed ⟨hu5, hu6⟩,
        forall_mem_set hW'.log hlog', hns0.chain, hns0.ledLog_len, hns0.ledLog, hns0.config, hns0.ledConf_len,
        hns0.ledConf, hns0.ledAt, hns0.elAt, hns0.termLen, ?_, fun f hf => hW.msgs f (bootSend_mem_lsetMinus hf),
        ?_, fun v hv => hW.votes v (bootSend_mem_lsetMinus hv), hns0.leaders_len, hns0.leaders, hns0.undo,
        hns0.pending, hns0.queue, hns0.reads, hns0.viol⟩
      · show (lset.minus s.msgs u.msgs).length ≤ 2 * (b + ev.weight); have := bootSend_lsetMinus_length s.msgs u.msgs; have := hW.msgs_len; omega
      · show (lset.minus s.votes u.votes).length ≤ b + ev.weight; have := bootSend_lsetMinus_length s.votes u.votes; have := hW.votes_len; omega
    · show logWithin b E ((s.log.set n (pre ++ u.suffix))[n]!)
      by_cases hl : n < s.log.length
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hl]; exact hlog
      · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
        exact ⟨Nat.zero_le _, fun x hx => by cases hx⟩
  · exact bootSend_boot_tail hW hNO hb hns0 rfl hlog0 (by dsimp only; exact ho)

end AntCheck
end EtcdGrove
end Perennial
