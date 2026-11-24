/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the budget law of `ReadAsked` (`State.readAsked_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.readAsked_within : ActionWithin State.readAsked := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hw2 : 2 ≤ ev.weight := by unfold Event.weight; omega
  unfold numBound at hb
  unfold State.readAsked at ho
  obtain ⟨cx, -, ho⟩ := bind_ok ho
  simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho
  subst ho
  refine ⟨hW'.cfg, hW'.i_pos, hW'.i_le, hW'.currentTerm, hW'.voteTerm, hW'.commitIndex, hW'.lastApplied, hW'.confAt, hW'.confirmed, hW'.log, hW'.chain, hW'.ledLog_len, hW'.ledLog, hW'.config, hW'.ledConf_len, hW'.ledConf, hW'.ledAt, hW'.elAt, hW'.termLen, hW'.msgs_len, hW'.msgs, hW'.votes_len, hW'.votes, hW'.leaders_len, hW'.leaders, hW'.undo, hW'.pending, hW'.queue, ?_, hW'.viol⟩
  have hr : (s.reads[n]!).length ≤ b ∧ ∀ x ∈ s.reads[n]!, bigOk x.floor :=
    getElem!_mem' (α := List ReadRec) (P := fun (r : List ReadRec) => r.length ≤ b ∧ ∀ x ∈ r, bigOk x.floor) hW.reads
      ⟨Nat.zero_le _, fun x hx => by cases hx⟩
  have hfl : bigOk (s.chain.length : Int) := by have := hW.chain.1; unfold bigOk; omega
  refine forall_mem_set hW'.reads ?_
  split
  · refine ⟨?_, fun x hx => ?_⟩
    · rw [List.length_drop, List.length_append, List.length_singleton]; omega
    · have hx' := List.mem_of_mem_drop hx
      rcases List.mem_append.1 hx' with hx' | hx'
      · exact hr.2 x hx'
      · rw [List.mem_singleton] at hx'; subst hx'; exact hfl
  · rename_i hlen
    refine ⟨?_, fun x hx => ?_⟩
    · rw [List.length_append, List.length_singleton] at hlen ⊢; unfold maxReads at hlen; omega
    · rcases List.mem_append.1 hx with hx | hx
      · exact hr.2 x hx
      · rw [List.mem_singleton] at hx; subst hx; exact hfl

end AntCheck
end EtcdGrove
end Perennial
