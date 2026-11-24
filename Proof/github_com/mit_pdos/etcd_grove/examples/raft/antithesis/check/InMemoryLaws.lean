/-
Lean-first (no Rocq counterpart). #33 S3b W3b (2026-11-23): pure laws for the proof of
`State.InMemory` (`State__InMemory.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.InMemory

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

set_option linter.unusedSimpArgs false

/-- `\E` over the list from position `j`: its element `j`, then the rest. -/
theorem anyM_drop_succ {α : Type} [Inhabited α] (l : List α) (f : α → EvalM Bool) {j : Nat} (hj : j < l.length) :
    anyM (l.drop j) f = (do if (← f l[j]!) then pure true else anyM (l.drop (j + 1)) f) := by
  rw [List.drop_eq_getElem_cons hj, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- `InMemory`'s result keeps the per-server lists' lengths (`role`, `config`, `confAt`: one
position set). -/
theorem State.inMemory_lengths : ∀ (s : State) (n : Nat) (ev : Event) (r : MemResult),
    s.inMemory n ev = .ok r → r.role.length = s.role.length ∧ r.config.length = s.config.length ∧
      r.confAt.length = s.confAt.length := by
  intro s n ev r h
  unfold State.inMemory at h
  replace h := bind_ok h; obtain ⟨ok, -, h⟩ := h
  replace h := bind_ok h; obtain ⟨r1, -, h⟩ := h
  replace h := bind_ok h; obtain ⟨ld, -, h⟩ := h
  replace h := bind_ok h; obtain ⟨l2, -, h⟩ := h
  replace h := bind_ok h; obtain ⟨lc, -, h⟩ := h
  extract_lets viol0 lc0 me vCS jp1 at h
  have : ∃ cc : List Conf × List Int, cc.1.length = s.config.length ∧ cc.2.length = s.confAt.length ∧
      jp1 cc = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨sn, -, h⟩ := h
      replace h := bind_ok h; obtain ⟨c, -, h⟩ := h
      replace h := bind_ok h; obtain ⟨sn', -, h⟩ := h
      replace h := bind_ok h; obtain ⟨a, -, h⟩ := h
      replace h := bind_ok h; obtain ⟨cc, hcc, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hcc
      subst hcc
      exact ⟨(s.config.set n c, s.confAt.set n a), List.length_set .., List.length_set .., h⟩
    · replace h := bind_ok h; obtain ⟨cc, hcc, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hcc
      subst hcc
      exact ⟨(s.config, s.confAt), rfl, rfl, h⟩
  obtain ⟨⟨config, confAt⟩, hcf, hca, h⟩ := this
  simp -zeta only [jp1] at h
  replace h := bind_ok h; obtain ⟨w, -, h⟩ := h
  extract_lets jp2 at h
  have : ∃ p : TermFn Int × TermFn Int, jp2 p = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨t, -, h⟩ := h
      replace h := bind_ok h; obtain ⟨t', -, h⟩ := h
      replace h := bind_ok h; obtain ⟨p, hp, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hp
      subst hp
      exact ⟨(s.ledAt.with t s.confAt[n]!, s.elAt.with t' s.confAt[n]!), h⟩
    · replace h := bind_ok h; obtain ⟨p, hp, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hp
      subst hp
      exact ⟨(s.ledAt, s.elAt), h⟩
  obtain ⟨⟨ledAt, elAt⟩, h⟩ := this
  simp -zeta only [jp2] at h
  replace h := bind_ok h; obtain ⟨cd, -, h⟩ := h
  extract_lets jp3 at h
  have : ∃ ch : List Entry, jp3 ch = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨ch, -, h⟩ := h
      exact ⟨ch, h⟩
    · replace h := bind_ok h; obtain ⟨ch, hch, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at hch
      subst hch
      exact ⟨s.chain, h⟩
  obtain ⟨chain, h⟩ := this
  simp -zeta only [jp3] at h
  replace h := bind_ok h; obtain ⟨cm, -, h⟩ := h
  extract_lets jp4 at h
  have : ∃ tl : TermFn Int, jp4 tl = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨t, -, h⟩ := h
      replace h := bind_ok h; obtain ⟨c, -, h⟩ := h
      replace h := bind_ok h; obtain ⟨tl, htl, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at htl
      subst htl
      exact ⟨s.termLen.with t c, h⟩
    · replace h := bind_ok h; obtain ⟨tl, htl, h⟩ := h
      simp only [pure_ok, Except.ok.injEq] at htl
      subst htl
      exact ⟨s.termLen, h⟩
  obtain ⟨termLen, h⟩ := this
  simp -zeta only [jp4] at h
  replace h := bind_ok h; obtain ⟨d1, -, h⟩ := h
  extract_lets jpF jpU jp5 at h
  have : ∃ v : SSet, jp5 () v = .ok r := by
    split at h
    · exact ⟨vCS, h⟩
    · exact ⟨viol0, h⟩
  obtain ⟨v1, h⟩ := this
  simp -zeta only [jp5] at h
  replace h := bind_ok h; obtain ⟨d2, -, h⟩ := h
  extract_lets vLC jp7 jp6 at h
  have : ∃ l : Bool, jp6 () l = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨_, -, h⟩ := h
      replace h := bind_ok h; obtain ⟨l, -, h⟩ := h
      exact ⟨l, h⟩
    · exact ⟨_, h⟩
  clear h
  obtain ⟨l1, h⟩ := this
  simp -zeta only [jp6] at h
  replace h := bind_ok h; obtain ⟨d3, -, h⟩ := h
  have : ∃ l : Bool, jp7 () l = .ok r := by
    split at h
    · replace h := bind_ok h; obtain ⟨l, -, h⟩ := h
      exact ⟨l, h⟩
    · exact ⟨_, h⟩
  clear h
  obtain ⟨l2', h⟩ := this
  simp -zeta only [jp7] at h
  have : ∃ v : SSet, jpU () v = .ok r := by
    split at h
    · exact ⟨vLC, h⟩
    · exact ⟨v1, h⟩
  clear h
  obtain ⟨v2, h⟩ := this
  simp -zeta only [jpU] at h
  replace h := bind_ok h; obtain ⟨_, -, h⟩ := h
  have : ∃ v : SSet, jpF () v = .ok r := by
    split at h
    · exact ⟨_, h⟩
    · exact ⟨v2, h⟩
  clear h
  obtain ⟨v3, h⟩ := this
  simp -zeta only [jpF, pure_ok, Except.ok.injEq] at h
  subst h
  exact ⟨List.length_set .., hcf, hca⟩

end AntCheck
end EtcdGrove
end Perennial
