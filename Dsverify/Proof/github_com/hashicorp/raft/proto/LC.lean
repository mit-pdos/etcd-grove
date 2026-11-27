/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/LC.lean (241f27e).
-/
/-
`proto` — leader completeness. `ILC` is a consequence of the other conjuncts of `PInv`
(`ILC_of`): by strong induction on the later term, its election quorum meets the acknowledgement
quorum, `VoteAck` gives the voter's log the prefix (no leader in between lacks it, by induction),
and the up-to-date check transfers it to the leader's election log (`utd`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Invariant
public import Dsverify.Proof.github_com.hashicorp.raft.proto.Lemmas

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ### Shape of the leader logs -/

theorem leader_ge_two {σ : PState} (hL : ILeaders σ) {T : Nat} (h : σ.leader T ≠ none) : 2 ≤ T := by
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp h
  exact (hL.1 T ℓ hℓ).2.1

/-- Every entry of `llog t` has term `≤ t`. -/
theorem llog_term_le {σ : PState} (hG : IGen σ) (hL : ILeaders σ) {t k : Nat} (h1 : 1 ≤ k)
    (h2 : k ≤ (σ.llog t).length) : termAt (σ.llog t) k ≤ t := by
  cases hl : σ.leader t with
  | some ℓ =>
    obtain ⟨_, _, _, _, _, hel, hown, _⟩ := hL.1 t ℓ hl
    by_cases hk : k ≤ σ.len0 t
    · exact Nat.le_of_lt (hel k h1 hk)
    · obtain ⟨e, he⟩ := ent_isSome _ k h1 h2
      rw [termAt_of_ent he, hown k e (by omega) he]
      exact Nat.le_refl _
  | none =>
    by_cases ht : t = 1
    · subst ht
      rw [hG.2.2.2.2.1] at h2 ⊢
      simp at h2
      have : k = 1 := by omega
      subst this
      simp [termAt, ent, hG.1]
    · rw [hL.2 t ht hl] at h2
      simp at h2
      omega

/-- An entry of term `t` in `llog t` is one of the leader's own entries. -/
theorem llog_own_gt_len0 {σ : PState} (hL : ILeaders σ) {t k : Nat} {ℓ : SID} (hl : σ.leader t = some ℓ)
    (h1 : 1 ≤ k) (ht : termAt (σ.llog t) k = t) : σ.len0 t < k := by
  obtain ⟨_, _, _, _, _, hel, _⟩ := hL.1 t ℓ hl
  apply Classical.byContradiction
  intro hn
  have := hel k h1 (by omega)
  omega

theorem llog_leader {σ : PState} (hL : ILeaders σ) {t : Nat} (ht : t ≠ 1) (hne : 1 ≤ (σ.llog t).length) :
    σ.leader t ≠ none := by
  intro hn
  rw [hL.2 t ht hn] at hne
  simp at hne

/-- Terms are nondecreasing along an `LMok` log. -/
theorem LMok_term_mono {σ : PState} (hG : IGen σ) (hL : ILeaders σ) {L : RLog} (hM : LMok σ L)
    {k k' : Nat} (hk : 1 ≤ k) (hkk : k ≤ k') (hk' : k' ≤ L.length) : termAt L k ≤ termAt L k' := by
  have a := hM k' (by omega) hk'
  rw [agree_termAt a hkk]
  exact llog_term_le hG hL hk (by have := a.2.1; omega)

/-! ### The up-to-date transfer -/

/-- If `L` has the prefix `llog T0 [1..k]` (its last entry of term `T0`), `E` is at least as up to
date as `L`, every entry of `E` has a term `< Tb` and no leader of a term in `(T0, Tb)` lacks the
prefix, then `E` has it. -/
theorem utd {σ : PState} (hG : IGen σ) (hL : ILeaders σ) {T0 k Tb : Nat} {E L : RLog}
    (hT0 : σ.leader T0 ≠ none) (hk : 1 ≤ k) (hkT0 : termAt (σ.llog T0) k = T0)
    (hE : LMok σ E) (hEb : ∀ x, 1 ≤ x → x ≤ E.length → termAt E x < Tb)
    (hLm : LMok σ L) (hag : agree L (σ.llog T0) k) (hu : upToDate E.length (lastTerm E) L)
    (H : ∀ t, T0 < t → t < Tb → σ.leader t ≠ none → ¬ lacks σ t k T0) :
    agree E (σ.llog T0) k := by
  have hkL : k ≤ L.length := hag.1
  have htk : termAt L k = T0 := (agree_termAt hag (Nat.le_refl _)).trans hkT0
  have hmono : T0 ≤ lastTerm L := by
    have := LMok_term_mono hG hL hLm hk hkL (Nat.le_refl _)
    unfold lastTerm; omega
  have h2 := leader_ge_two hL hT0
  rcases hu with hlt | ⟨heq, hlen⟩
  · -- `E`'s last term is newer: go through the leader of that term
    have hn : 1 ≤ E.length := by
      apply Classical.byContradiction; intro hn
      have : E.length = 0 := by omega
      unfold lastTerm at hlt; rw [this, termAt_zero] at hlt; omega
    have hEa := hE E.length hn (Nat.le_refl _)
    have hlt' : lastTerm E = termAt E E.length := rfl
    rw [← hlt'] at hEa
    have hld : σ.leader (lastTerm E) ≠ none :=
      llog_leader hL (by omega) (by have := hEa.2.1; omega)
    have hb : lastTerm E < Tb := hEb _ hn (Nat.le_refl _)
    have hnl := H _ (by omega) hb hld
    unfold lacks at hnl
    have ⟨hk0, hag2⟩ := Classical.not_not.mp hnl
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hld
    have htE : termAt (σ.llog (lastTerm E)) E.length = lastTerm E :=
      (agree_termAt hEa (Nat.le_refl _)).symm
    have := llog_own_gt_len0 hL hℓ hn htE
    exact agree_trans (agree_mono hEa (by omega)) hag2
  · have hnL : 1 ≤ L.length := by omega
    have hLa := hLm L.length hnL (Nat.le_refl _)
    have hEa := hE E.length (by omega) (Nat.le_refl _)
    have e1 : termAt L L.length = lastTerm L := rfl
    have e2 : termAt E E.length = lastTerm E := rfl
    rw [e1] at hLa
    rw [e2, ← heq] at hEa
    have hEL : agree E L L.length := agree_trans (agree_mono hEa hlen) (agree_symm hLa)
    exact agree_trans (agree_mono hEL hkL) hag

/-! ### Leader completeness from the other conjuncts -/

/- stage-4: `ILC_of` moved to `CL0.lean` (it needs `CL0`), with the R-commits (`ICfgR`) and the
recorded commits (`ICommits`' first part) as new hypotheses. Old statement:
theorem ILC_of {σ : PState} (hG : IGen σ) (hL : ILeaders σ) (hLo : ILogs σ) (hV : IVotes σ)
    (hVA : IVoteAck σ) : ILC σ := by
-/
  /- stage-3 proof:
  := by
  intro T k hc T'
  induction T' using Nat.strongRecOn with
  | _ T' IH =>
  intro hTT' hld hlacks
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hld
  obtain ⟨_, _, _, hlen0, _, hel, _, hcand, QE, hQE, hQEv⟩ := hL.1 T' ℓ hℓ
  obtain ⟨hcT, hk1, hkl, hkt, Q, hQ, hQa⟩ := hc
  obtain ⟨j, hjQ, hjE⟩ := quorum_inter hQ hQE
  obtain ⟨m, hkm, ha⟩ := hQa j hjQ
  obtain ⟨L, hv⟩ := hQEv j hjE
  have hLag : agree L (σ.llog T) k := by
    rcases hVA j T' ℓ L true T m k hv ha hkm hTT' with h | ⟨T'', h1, h2, h3, h4⟩
    · exact h
    · rcases h2 with h2 | ⟨_, h2⟩
      · exact absurd h4 (IH T'' h2 h1 h3)
      · cases h2
  obtain ⟨li, lt, hc', hu⟩ := (hV.1 j T' ℓ L true hv).2.2.2.1
  rw [hcand] at hc'
  cases hc'
  let E := (σ.llog T').take (σ.len0 T')
  have hElen : E.length = σ.len0 T' := by simp [E]; omega
  have hE : LMok σ E := LMok_take (hLo.2.1 T') _
  have hEb : ∀ x, 1 ≤ x → x ≤ E.length → termAt E x < T' := by
    intro x h1 h2
    rw [hElen] at h2
    simp only [E]
    rw [termAt_take _ _ _ h2]
    exact hel x h1 h2
  have hu' : upToDate E.length (lastTerm E) L := by rw [hElen]; exact hu
  have hag := utd hG hL hcT hk1 hkt hE hEb (hLo.2.2.1 j T' ℓ L true hv) hLag hu'
    (fun t h1 h2 h3 => IH t h2 h1 h3)
  apply hlacks
  refine ⟨?_, agree_of_take hag⟩
  have := hag.1
  omega
  -/

/-- Two committed prefixes agree up to the shorter one. -/
theorem committed_agree {σ : PState} (hLC : ILC σ) {T0 n p0 T k p : Nat} (h0 : committed σ T0 n p0)
    (ha0 : cfgAdm σ T0 n p0) (h : committed σ T k p) (ha : cfgAdm σ T k p) (hkn : k ≤ n) :
    agree (σ.llog T0) (σ.llog T) k := by
  rcases Nat.lt_trichotomy T T0 with hlt | heq | hgt
  · have := hLC T k p h ha T0 hlt h0.1
    unfold lacks at this
    exact (Classical.not_not.mp this).2
  · subst heq
    exact agree_refl _ _ (by have := h.2.2.1; omega)
  · have := hLC T0 n p0 h0 ha0 T hgt h.1
    unfold lacks at this
    exact agree_symm (agree_mono (Classical.not_not.mp this).2 hkn)

end proto
end github_com.hashicorp.raft
end Perennial
