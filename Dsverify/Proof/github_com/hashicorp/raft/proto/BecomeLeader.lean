/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/BecomeLeader.lean (241f27e).
-/
/-
`proto` — `becomeLeader` preserves `PInv` (the new leader's election log has terms `< T`, every
election vote is early; leader completeness for the new leader is `ILC_of`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Frame

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-- No entry of term `t` in an `LMok` log when `llog t = []`. -/
theorem LMok_no_term {σ : PState} {L : RLog} (h : LMok σ L) {t : Nat} (ht : σ.llog t = []) {k : Nat}
    (h1 : 1 ≤ k) (h2 : k ≤ L.length) : termAt L k ≠ t := by
  intro he
  have := (h k h1 h2).2.1
  rw [he, ht] at this
  simp at this
  omega

/-- The state after a real election (stage 4: the commitment counts the latest configuration). -/
abbrev blS (σ : PState) (c : SID) : PState :=
  { σ with leader := updT σ.leader (σ.term c) (some c),
           llog := updT σ.llog (σ.term c) (σ.log c),
           len0 := updT σ.len0 (σ.term c) (σ.log c).length,
           ccfg := updT σ.ccfg (σ.term c) (lastCfgIdx (σ.log c)) }

theorem becomeLeader_eq {σ : PState} {c : SID} (hn : σ.leader (σ.term c) = none) :
    becomeLeader σ c = blS σ c := by
  simp [becomeLeader, hn]

section
variable {σ : PState} {c : SID} (h : PInv σ) (hp : becomeLeaderPre σ c)
  (hn : σ.leader (σ.term c) = none)
include h hp hn

/-- The new leader's log is not empty: its configuration has a quorum. -/
theorem bl_log_ne : 1 ≤ (σ.log c).length := by
  obtain ⟨_, _, Q, hQ, _⟩ := hp
  apply Classical.byContradiction; intro h0
  have : σ.log c = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [this, cfgOf_nil] at hQ
  exact not_quorum_nil Q hQ

theorem bl_T2 : 2 ≤ σ.term c := by
  have hne := bl_log_ne h hp hn
  obtain ⟨_, _, _, _, hV, _⟩ := h
  obtain ⟨_, hc, _⟩ := hp
  have ⟨_, h1, _, h3, _⟩ := hV.2.2 c _ _ hc
  apply Classical.byContradiction; intro hlt
  have := h3 (by omega)
  simp at this; omega

theorem bl_llogT : σ.llog (σ.term c) = [] := by
  have := bl_T2 h hp hn
  obtain ⟨_, hL, _⟩ := h
  exact hL.2 _ (by omega) hn

theorem bl_terms : ∀ k, 1 ≤ k → k ≤ (σ.log c).length → termAt (σ.log c) k < σ.term c := by
  intro k h1 h2
  have hT := bl_llogT h hp hn
  obtain ⟨_, _, hLo, _, _, _, _, _, _, _, _, hX, _⟩ := h
  have a := (hX c hp.1).2 k h1 h2
  have b := LMok_no_term (hLo.1 c hp.1).1 hT h1 h2
  omega

theorem bl_prefix : ∀ t, σ.llog t <+: (blS σ c).llog t := by
  intro t
  by_cases ht : t = σ.term c
  · subst ht
    simp only [updT_same, bl_llogT h hp hn]
    exact List.nil_prefix
  · simp only [updT_ne _ _ _ _ ht]
    exact List.prefix_refl _

theorem bl_HG : HG σ (blS σ c) := by
  refine ⟨rfl, ?_, bl_prefix h hp hn, ?_, rfl⟩
  · intro T ℓ hl
    have : T ≠ σ.term c := by intro e; subst e; rw [hn] at hl; cases hl
    simp only [updT_ne _ _ _ _ this]; exact hl
  · intro T hl
    have : T ≠ σ.term c := by intro e; subst e; exact hl hn
    simp only [updT_ne _ _ _ _ this]

theorem bl_IGen : IGen (blS σ c) := by
  have hT := bl_T2 h hp hn
  obtain ⟨hG, _⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hG
  simp only [IGen]
  refine ⟨a1, a2, a3, a4, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [updT_ne _ _ _ _ (by omega)]; assumption)

theorem bl_ILeaders : ILeaders (blS σ c) := by
  have hT := bl_T2 h hp hn
  have hterms := bl_terms h hp hn
  have hne := bl_log_ne h hp hn
  obtain ⟨hG, hL, hLo, _, hV, _⟩ := h
  obtain ⟨hc, hcand, Q, hQ, hQv⟩ := hp
  constructor
  · intro T1 ℓ hl
    by_cases hT1 : T1 = σ.term c
    · subst hT1
      have hadm : cfgAdmAt (blS σ c) (σ.term c) ((blS σ c).llog (σ.term c)).length
          ((blS σ c).ccfg (σ.term c)) := by
        left; simp only [updT_same, List.take_length]
      simp only [updT_same, Option.some.injEq] at hl hadm ⊢
      subst hl
      have hg1 : ent (σ.log c) 1 = some σ.g := by
        rcases (hLo.1 _ hc).2 with h0 | h0
        · rw [h0] at hne; simp at hne
        · exact h0
      refine ⟨hc, hT, hne, Nat.le_refl _, hg1, fun k h1 h2 => hterms k h1 h2, ?_, ?_, ⟨Q, ?_, ?_⟩, hadm⟩
      · intro k e hk he
        have := (ent_le_length he).2
        omega
      · rw [List.take_length]; exact hcand
      · rw [List.take_length]; exact hQ
      · intro j hj
        obtain ⟨L, b, hv⟩ := hQv j hj
        refine ⟨L, ?_⟩
        cases b with
        | true => exact hv
        | false => exact absurd hn ((hV.1 j _ _ L false hv).2.2.2.2 rfl)
    · have hl' : σ.leader T1 = some ℓ := by simpa [updT_ne _ _ _ _ hT1] using hl
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hL.1 T1 ℓ hl'
      have e1 : (blS σ c).llog T1 = σ.llog T1 := updT_ne _ _ _ _ hT1
      have e2 : (blS σ c).len0 T1 = σ.len0 T1 := updT_ne _ _ _ _ hT1
      have e3 : (blS σ c).ccfg T1 = σ.ccfg T1 := updT_ne _ _ _ _ hT1
      have a10' : cfgAdmAt (blS σ c) T1 (σ.llog T1).length ((blS σ c).ccfg T1) := by
        rw [cfgAdmAt_congr e1 e2, e3]; exact a10
      rw [e1, e2]
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10'⟩
  · intro T1 h1 hl
    by_cases hT1 : T1 = σ.term c
    · subst hT1; simp at hl
    · simp only [updT_ne _ _ _ _ hT1] at hl ⊢
      exact hL.2 T1 h1 hl

theorem bl_ILogs : ILogs (blS σ c) := by
  have hpre := bl_prefix h hp hn
  obtain ⟨hG, hL, hLo, _⟩ := h
  obtain ⟨l1, l2, l3, l4, l5⟩ := hLo
  refine ⟨fun i hi => ⟨LMok_mono hpre (l1 i hi).1, (l1 i hi).2⟩, ?_,
    fun j T c' L b hv => LMok_mono hpre (l3 j T c' L b hv), LMok_mono hpre l4, ?_⟩
  · intro T
    by_cases hT : T = σ.term c
    · subst hT; simp only [updT_same]
      exact LMok_mono hpre (l1 c hp.1).1
    · simp only [updT_ne _ _ _ _ hT]
      exact LMok_mono hpre (l2 T)
  · intro T k e he hk
    by_cases hT : T = σ.term c
    · subst hT; simp only [updT_same] at he
      have := cfgAt_valid hG hL ⟨l1, l2, l3, l4, l5⟩ (l1 c hp.1).1 ((isCfgAt_iff _ _).mpr ⟨e, he, hk⟩)
      simpa [cfgAt, cfgAtC, he] using this
    · simp only [updT_ne _ _ _ _ hT] at he
      exact l5 T k e he hk

theorem bl_ICfgR : ICfgR (blS σ c) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := h
  intro T1 p e h1 h2 h3 h4
  by_cases hT1 : T1 = σ.term c
  · subst hT1
    simp only [updT_same] at h2 h3
    have := (ent_le_length h3).2
    omega
  · have e1 : (blS σ c).llog T1 = σ.llog T1 := updT_ne _ _ _ _ hT1
    have e2 : (blS σ c).len0 T1 = σ.len0 T1 := updT_ne _ _ _ _ hT1
    have h1' : σ.leader T1 ≠ none := by simpa [updT_ne _ _ _ _ hT1] using h1
    rw [e1] at h3; rw [e2] at h2
    obtain ⟨hadj, k, pc, q, hc, a, b, c', d, f⟩ := hR T1 p e h1' h2 h3 h4
    refine ⟨?_, k, pc, q, hc, by rw [e2]; exact a, by rw [e1]; exact b, c', d, ?_⟩
    · rw [e1]; exact hadj
    · rw [cfgAdmAt_congr e1 e2]; exact f

theorem bl_ICurrent : ICurrent (blS σ c) := by
  obtain ⟨_, _, _, hC, _⟩ := h
  intro i hi hl
  by_cases hT : σ.term i = σ.term c
  · have hl' : (blS σ c).leader (σ.term i) = some i := hl
    simp only [hT, updT_same, Option.some.injEq] at hl'
    subst hl'
    show σ.log c = updT σ.llog (σ.term c) (σ.log c) (σ.term c)
    simp
  · have hl' : (blS σ c).leader (σ.term i) = some i := hl
    simp only [updT_ne _ _ _ _ hT] at hl'
    show σ.log i = updT σ.llog (σ.term c) (σ.log c) (σ.term i)
    rw [updT_ne _ _ _ _ hT]
    exact hC i hi hl'

theorem bl_IVotes : IVotes (blS σ c) := by
  have hg := bl_HG h hp hn
  obtain ⟨_, _, _, _, hV, _⟩ := h
  refine ⟨fun j T c' L b hv => ?_, hV.2.1, hV.2.2⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := hV.1 j T c' L b hv
  exact ⟨a1, a2, a3, a4, fun hb => hg.ne_none (a5 hb)⟩

theorem bl_IBounds : IBounds (blS σ c) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hB, _⟩ := h
  obtain ⟨b1, b2, b3, b4, b5⟩ := hB
  refine ⟨b1, ?_, ?_, b4, b5⟩
  · intro T
    by_cases hT : T = σ.term c
    · subst hT; simp only [updT_same]; exact (b1 c hp.1).2
    · simp only [updT_ne _ _ _ _ hT]; exact b2 T
  · intro T hT
    have hT' : σ.maxT < T := hT
    have : T ≠ σ.term c := by have := (b1 c hp.1).1; omega
    simp only [updT_ne _ _ _ _ this]
    exact b3 T hT'

theorem bl_inv : PInv (blS σ c) := by
  have hg := bl_HG h hp hn
  have hG' := bl_IGen h hp hn
  have hL' := bl_ILeaders h hp hn
  have hLo' := bl_ILogs h hp hn
  have hV' := bl_IVotes h hp hn
  have hC' := bl_ICurrent h hp hn
  have hB' := bl_IBounds h hp hn
  have hR' := bl_ICfgR h hp hn
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  have hA' : IAcks (blS σ c) :=
    IAcks_grow hg hL (fun j _ => List.prefix_refl _) (fun j _ => Nat.le_refl _) (fun _ _ _ x => x) hA
  have hVA' : IVoteAck (blS σ c) :=
    IVoteAck_grow hg hL hA (fun _ _ _ x => x) (fun _ _ _ x => x) hVA
  have hCo' : ICommits (blS σ c) := ICommits_grow hg (fun _ _ _ x => x) (fun _ _ _ => Iff.rfl) rfl hCo
  exact ⟨hG', hL', hLo', hC', hV', hA', hVA',
    ILC_of hG' hL' hLo' hV' hVA' hR' (fun T k p hc => ⟨(hCo'.1 T k p hc).1, (hCo'.1 T k p hc).2.1⟩),
    hCo',
    IDur_grow hg (fun j _ => List.prefix_refl _) (fun j _ => Nat.le_refl _)
      (fun j _ => ⟨rfl, rfl⟩) (fun _ _ _ x => x) hD, hB', hX,
    IPub_grow hg (fun j _ => Nat.le_refl _) (fun j _ => rfl) (fun _ _ _ x => x) rfl hP, hR'⟩

theorem bl_grows : Grows σ (blS σ c) := by
  have hg := bl_HG h hp hn
  refine ⟨rfl, ⟨rfl, rfl⟩, hg.leader, fun T => ⟨hg.llog T, ?_⟩, fun _ _ _ x => x, fun _ _ _ x => x,
    fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _, fun _ => Nat.le_refl _,
    fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ x => x,
    fun _ _ _ _ x => Or.inl x⟩
  intro hT
  rcases hT with hT | hT
  · exact hg.len0 T hT
  · have := bl_T2 h hp hn
    have : T ≠ σ.term c := by omega
    simp only [updT_ne _ _ _ _ this]

end

theorem becomeLeader_inv' (σ : PState) (c : SID) (h : PInv σ) (hp : becomeLeaderPre σ c) :
    PInv (becomeLeader σ c) ∧ Grows σ (becomeLeader σ c) := by
  by_cases hn : σ.leader (σ.term c) = none
  · rw [becomeLeader_eq hn]
    exact ⟨bl_inv h hp hn, bl_grows h hp hn⟩
  · have : becomeLeader σ c = σ := by simp [becomeLeader, hn]
    rw [this]
    refine ⟨h, rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ x => x,
      fun _ _ _ _ x => Or.inl x⟩

end proto
end github_com.hashicorp.raft
end Perennial
