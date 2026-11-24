/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the budget law of `Mem`
(`State.mem_within_of`, over `InMemory`'s, `State.inMemory_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.W6Laws

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

theorem State.mem_within_of (inMemory_within : InMemoryWithin) : ActionWithin State.mem := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  have hw2 : ev.weight = ev.size + 2 := rfl
  unfold State.mem at ho
  obtain ⟨r, hr, ho⟩ := bind_ok ho
  have hrW := inMemory_within s n ev b E r hn hW hNO hCh hb hr
  split at ho
  · cases ho
  obtain ⟨wv, -, ho⟩ := bind_ok ho
  have hW' := State.Within.mono' (b' := b + ev.weight) (E' := E) (by omega) (Nat.le_refl _) hW
  have hrW' : r.Within (b + ev.weight) E s := by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13⟩ := hrW
    exact ⟨by omega, r2, by omega, fun p hp => ⟨(r4 p hp).1, (r4 p hp).2.mono' (by omega) (Nat.le_refl _)⟩,
      by omega, fun p hp => ⟨(r6 p hp).1, (r6 p hp).2.mono' (by omega) (Nat.le_refl _)⟩,
      fun c hc => (r7 c hc).mono' (by omega) (Nat.le_refl _), r8, r9.mono' (by omega), r10.mono' (by omega),
      r11.mono' (by omega), r12.mono' (by omega) (Nat.le_refl _), r13⟩
  split at ho
  · obtain ⟨qi, hqi, ho⟩ := bind_ok ho
    simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    have hv0 : r.viol.length ≤ b + ev.weight := by simp only at hv; rw [hv]; simp
    -- the queued item: the report and `n`'s pending messages (or none)
    have hqiW : qi.ev.Within (b + ev.weight) E ∧ qi.m.length ≤ b + ev.weight ∧
        ∀ m ∈ qi.m, m.Within (b + ev.weight) E := by
      unfold State.queued at hqi
      obtain ⟨by_, -, hqi⟩ := bind_ok hqi
      have hevW : ev.Within (b + ev.weight) E := ⟨hNO, by omega, hCh⟩
      have hpm := getElem!_mem' (l := s.pending) (n := n)
        (P := fun ms : List Msg => ms.length ≤ b + ev.weight ∧ ∀ m ∈ ms, m.Within (b + ev.weight) E)
        hW'.pending ⟨Nat.zero_le _, fun m hm => (List.not_mem_nil hm).elim⟩
      split at hqi <;> simp only [pure_ok, Except.ok.injEq] at hqi <;> subst hqi
      · exact ⟨hevW, hpm.1, hpm.2⟩
      · exact ⟨hevW, Nat.zero_le _, fun m hm => (List.not_mem_nil hm).elim⟩
    refine W6Laws.within_mem hW' hrW' hv0 (fun x hx => ?_)
    rcases mem_set_or hx with h | h
    · subst h
      have hq := getElem!_mem' (l := s.queue) (n := n)
        (P := fun q : List QItem => q.length ≤ b ∧ ∀ it ∈ q, it.ev.Within b E ∧ it.m.length ≤ b ∧ ∀ m ∈ it.m, m.Within b E)
        hW.queue ⟨Nat.zero_le _, fun it hit => (List.not_mem_nil hit).elim⟩
      refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun it hit => ?_⟩
      rcases List.mem_append.1 hit with hit | hit
      · obtain ⟨i1, i2, i3⟩ := hq.2 it hit
        exact ⟨i1.mono' (by omega) (Nat.le_refl _), by omega, fun m hm => (i3 m hm).mono' (by omega) (Nat.le_refl _)⟩
      · simp at hit; subst hit; exact hqiW
    · exact hW'.queue x h
  · simp only [pure_ok, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    have hv0 : r.viol.length ≤ b + ev.weight := by simp only at hv; rw [hv]; simp
    exact W6Laws.within_mem hW' hrW' hv0 hW'.queue

end AntCheck
end EtcdGrove
end Perennial
