/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Laws.lean (241f27e).
-/
/-
`proto` — the facts of `PInv` the code's proofs use (the laws). The code never unfolds `PInv`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Steps

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ### Logs -/

/-- Every server's log is empty or starts with the genesis entry (stage 4: a non-member starts
empty). -/
theorem log_genesis (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → σ.log i = [] ∨ ent (σ.log i) 1 = some σ.g := by
  intro h hi
  exact (h.2.2.1.1 i hi).2

/- stage-4 interface: false with membership changes (configuration entries anywhere), replaced by
`log_cfg_valid`; proved at stage3-final:
/-- A configuration entry in a server's log is the genesis, at index 1. -/
theorem log_config_one (σ : PState) (i : SID) (k : Nat) (e : Entry) :
    PInv σ → i ∈ σ.voters → ent (σ.log i) k = some e → e.kind = kConfig → k = 1 := by
  intro h hi he hk
  exact h.2.2.1.2.2.2.2.1 i hi k e he hk
-/

/-- (stage 4) A configuration entry in a server's log is a valid configuration over the servers
(`ICfgOk` through log matching). -/
theorem log_cfg_valid (σ : PState) (i : SID) (k : Nat) (e : Entry) :
    PInv σ → i ∈ σ.srvs → ent (σ.log i) k = some e → e.kind = kConfig →
      cfgValid σ.srvs (σ.cv e.data) := by
  intro h hi he hk
  obtain ⟨hG, hL, hLo, _⟩ := h
  have := cfgAt_valid hG hL hLo (hLo.1 i hi).1 ((isCfgAt_iff _ _).mpr ⟨e, he, hk⟩)
  simpa [cfgAt, cfgAtC, he] using this

/-- The leader of its current term has the leader log as its log. -/
theorem leader_log (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → σ.leader (σ.term i) = some i → σ.log i = σ.llog (σ.term i) := by
  intro h hi hl
  exact h.2.2.2.1 i hi hl

/-- The entries a leader appended in its term have its term. -/
theorem leader_own_term (σ : PState) (T k : Nat) (ℓ : SID) :
    PInv σ → σ.leader T = some ℓ → σ.len0 T < k → k ≤ (σ.llog T).length →
      termAt (σ.llog T) k = T := by
  intro h hl hk hkl
  obtain ⟨e, he⟩ := ent_isSome _ k (by omega) hkl
  rw [termAt_of_ent he]
  exact (h.2.1.1 T ℓ hl).2.2.2.2.2.2.1 k e hk he
  /- stage-3 proof:
  := by
  intro h hl hk hkl
  obtain ⟨e, he⟩ := ent_isSome _ k (by omega) hkl
  rw [termAt_of_ent he]
  exact ((h.2.1.1 T ℓ hl).2.2.2.2.2.2.1 k e hk he).1
  -/

/-- Just after the election, the leader log is the election-time log. -/
theorem becomeLeader_len0 (σ : PState) (c : SID) :
    PInv σ → becomeLeaderPre σ c →
      (becomeLeader σ c).leader (σ.term c) = some c ∧
      (becomeLeader σ c).len0 (σ.term c) = (σ.log c).length := by
  intro h hp
  by_cases hn : σ.leader (σ.term c) = none
  · rw [becomeLeader_eq hn]
    exact ⟨by simp, by simp⟩
  · have e : becomeLeader σ c = σ := by simp [becomeLeader, hn]
    rw [e]
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hn
    obtain ⟨_, _, _, _, _, _, _, hcand, _⟩ := h.2.1.1 _ ℓ hℓ
    obtain ⟨hc, hcc, Q, hQ, hQv⟩ := hp
    -- election safety (HUB-REQUEST P4-1 inside `elect_safety`: false without it, see
    -- notes/hub-requests-s4.md)
    have hM : LMok σ (σ.log c) := (h.2.2.1.1 c hc).1
    have := elect_safety σ h _ ℓ c (σ.log c) Q hℓ hM hcc hQ hQv
    subst this
    rw [hcc] at hcand
    exact ⟨hℓ, ((Prod.mk.inj (Option.some.inj hcand)).1).symm⟩
  /- stage-3 proof:
  := by
  intro h hp
  by_cases hn : σ.leader (σ.term c) = none
  · rw [becomeLeader_eq hn]
    exact ⟨by simp, by simp⟩
  · have e : becomeLeader σ c = σ := by simp [becomeLeader, hn]
    rw [e]
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hn
    obtain ⟨_, _, _, _, _, _, _, hcand, QE, hQE, hQEv⟩ := h.2.1.1 _ ℓ hℓ
    obtain ⟨hc, hcc, Q, hQ, hQv⟩ := hp
    obtain ⟨j, hj1, hj2⟩ := quorum_inter hQ hQE
    obtain ⟨L, b, hv⟩ := hQv j hj1
    obtain ⟨L', hv'⟩ := hQEv j hj2
    rw [hv] at hv'
    cases hv'
    rw [hcc] at hcand
    exact ⟨hℓ, ((Prod.mk.inj (Option.some.inj hcand)).1).symm⟩
  -/

/-- A term of a leader or of a candidate's election is at most `maxT` (so a term read from a
valid message can be adopted with `setTerm`). -/
theorem leader_le_maxT (σ : PState) (T : Nat) :
    PInv σ → σ.leader T ≠ none → T ≤ σ.maxT := by
  intro h hl
  apply Classical.byContradiction
  intro hn
  exact hl (h.2.2.2.2.2.2.2.2.2.2.1.2.2.1 T (by omega))

theorem cand_le_maxT (σ : PState) (c : SID) (T : Nat) (x : Nat × Nat) :
    PInv σ → σ.cand c T = some x → T ≤ σ.maxT := by
  intro h hc
  obtain ⟨hcv, _, hT⟩ := h.2.2.2.2.1.2.2 c T x hc
  have := (h.2.2.2.2.2.2.2.2.2.2.1.1 c hcv).1
  omega

theorem term_le_maxT (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → σ.term i ≤ σ.maxT := by
  intro h hi
  exact (h.2.2.2.2.2.2.2.2.2.2.1.1 i hi).1

/-- A server with a non-empty log has a term of at least 1 (stage 4: a non-member starts at term 0
with the empty log). -/
theorem term_ge_one (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → σ.log i ≠ [] → 1 ≤ σ.term i := by
  intro h hi
  exact (h.2.2.2.2.2.2.2.2.2.2.2.1 i hi).1

/-- (stage 4) A server's last log term is at most its term (`recordCandPre` after `newTerm`). -/
theorem lastTerm_le_term (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → lastTerm (σ.log i) ≤ σ.term i := by
  intro h hi
  by_cases hn : (σ.log i).length = 0
  · unfold lastTerm; rw [hn, termAt_zero]; exact Nat.zero_le _
  · exact (h.2.2.2.2.2.2.2.2.2.2.2.1 i hi).2 _ (by omega) (Nat.le_refl _)

/-- Log lengths are bounded by `maxI`. -/
theorem log_le_maxI (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → (σ.log i).length ≤ σ.maxI := by
  intro h hi
  exact (h.2.2.2.2.2.2.2.2.2.2.1.1 i hi).2

/-! ### AppendEntries, follower side -/

/- stage-4 interface: false with membership changes (a valid request may carry configuration
entries at any index; `ae_cfg_valid` gives their validity); proved at stage3-final:
/-- The entries of a valid request at index `≥ 2` are not configurations. -/
theorem ae_no_config (σ : PState) (T prev pt : Nat) (ents : RLog) (lci j : Nat) (e : Entry) :
    PInv σ → AEok σ T prev pt ents lci → ent ents j = some e → 2 ≤ prev + j →
      e.kind ≠ kConfig := by
  intro h hae he hj hk
  have hl := ent_le_length he
  rw [ae_slice hae hl.1 hl.2] at he
  have := h.2.2.1.2.2.2.2.2 T _ e he hk
  omega
-/

/-- (stage 4) A configuration entry of a valid request is a valid configuration over the servers
(`ICfgOk`). -/
theorem ae_cfg_valid (σ : PState) (T prev pt : Nat) (ents : RLog) (lci j : Nat) (e : Entry) :
    PInv σ → AEok σ T prev pt ents lci → ent ents j = some e → e.kind = kConfig →
      cfgValid σ.srvs (σ.cv e.data) := by
  intro h hae he hk
  have hl := ent_le_length he
  rw [ae_slice hae hl.1 hl.2] at he
  exact h.2.2.1.2.2.2.2 T _ e he hk

/-- After the follower has every entry of a valid request (previous entry matched), its log agrees
with the leader log up to the request's last index. -/
theorem ae_agree (σ : PState) (i : SID) (prev pt : Nat) (ents : RLog) (lci : Nat) :
    PInv σ → i ∈ σ.srvs → AEok σ (σ.term i) prev pt ents lci →
      prevMatch (σ.log i) prev pt → matchedUpTo (σ.log i) prev ents ents.length →
      agree (σ.log i) (σ.llog (σ.term i)) (prev + ents.length) := by
  intro h hi hae hpm hm
  apply ae_agree_upto h.2.2.1 hi hae hpm hm
  cases hn : ents.length with
  | zero =>
    rcases hpm with hp | ⟨hp, _⟩
    · omega
    · omega
  | succ n =>
    have := (hm.2 n (by omega)).1
    omega

/-- The follower may then learn the commit of `min lci v` for any `v` up to which it agrees. -/
theorem ae_learn (σ : PState) (i : SID) (prev pt : Nat) (ents : RLog) (lci v : Nat) :
    PInv σ → i ∈ σ.srvs → AEok σ (σ.term i) prev pt ents lci →
      agree (σ.log i) (σ.llog (σ.term i)) v → 0 < min lci v →
      ∃ T', learnCommitPre σ i (min lci v) T' := by
  intro h hi hae hag hpos
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', p', hT', hk', hc, hag'⟩, T'', k'', hT'', hk'', hpb⟩
  · omega
  · refine ⟨T', hi, hT', ⟨k', p', by omega, hc⟩, ?_, T'', k'', hT'', by omega, hpb⟩
    exact agree_trans (agree_mono hag (by omega)) (agree_mono hag' (by omega))
  /- stage-3 proof:
  := by
  intro h hi hae hag hpos
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', hT', hk', hc, hag'⟩, T'', k'', hT'', hk'', hpb⟩
  · omega
  · refine ⟨T', hi, hT', ⟨k', by omega, hc⟩, ?_, T'', k'', hT'', by omega, hpb⟩
    exact agree_trans (agree_mono hag (by omega)) (agree_mono hag' (by omega))
  -/

/-- A truncation never reaches the durable prefix (so no applied entry is deleted). -/
theorem truncate_gt_dur (σ : PState) (i : SID) (prev pt : Nat) (ents : RLog) (lci j : Nat) :
    PInv σ → truncatePre σ i prev pt ents lci j → (σ.srv i).dur.1 < prev + 1 + j := by
  intro h hp
  exact tr_gt_dur h hp

/-- The durable prefix is in the log. -/
theorem dur_le_log (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → (σ.srv i).dur.1 ≤ (σ.log i).length := by
  intro h hi
  rcases (h.2.2.2.2.2.2.2.2.2.1 i hi).1 with hd | ⟨_, _, hag⟩
  · omega
  · exact hag.1

/-! ### AppendEntries, leader side -/

/-- What a leader of its current term sends as `LeaderCommitIndex` (its `commitIndex`, at most
`cidx`) is covered as `AEok` requires. -/
theorem leader_lci (σ : PState) (ℓ : SID) (c : Nat) :
    PInv σ → ℓ ∈ σ.srvs → σ.leader (σ.term ℓ) = some ℓ → c ≤ (σ.srv ℓ).cidx →
      c = 0 ∨ ∃ T' k' p', T' ≤ σ.term ℓ ∧ c ≤ k' ∧ σ.commits T' k' p' ∧
        agree (σ.llog (σ.term ℓ)) (σ.llog T') c := by
  intro h hi hl hc
  obtain ⟨hd, hcx⟩ := h.2.2.2.2.2.2.2.2.2.1 ℓ hi
  by_cases hz : c = 0
  · exact Or.inl hz
  · rcases hd with hd | ⟨hT, ⟨k', p', hk', hck⟩, hag⟩
    · omega
    · right
      refine ⟨_, _, p', hT, by omega, hck, ?_⟩
      rw [← h.2.2.2.1 ℓ hi hl]
      exact agree_mono hag (by omega)
  /- stage-3 proof:
  := by
  intro h hi hl hc
  obtain ⟨hd, hcx⟩ := h.2.2.2.2.2.2.2.2.2.1 ℓ hi
  by_cases hz : c = 0
  · exact Or.inl hz
  · rcases hd with hd | ⟨hT, ⟨k', hk', hck⟩, hag⟩
    · omega
    · right
      refine ⟨_, _, hT, by omega, hck, ?_⟩
      rw [← h.2.2.2.1 ℓ hi hl]
      exact agree_mono hag (by omega)
  -/

/-- `AEok` is stable as the history grows. -/
theorem AEok_grows (σ σ' : PState) (T prev pt : Nat) (ents : RLog) (lci : Nat) :
    Grows σ σ' → AEok σ T prev pt ents lci → AEok σ' T prev pt ents lci := by
  intro hg hae
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, -, -, -, -, -, g14, -⟩ := hg
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hae
  have hp := (g4 T).1
  obtain ⟨X, hX⟩ := hp
  refine ⟨?_, ?_, a3, ?_, ?_, ?_⟩
  · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp a1
    rw [g3 T ℓ hℓ]; simp
  · rw [← hX]; simp; omega
  · intro h1; rw [← hX, termAt_append_left _ _ _ (by omega)]; exact a4 h1
  · rw [← hX, List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp; omega)]
    exact a5
  · rcases a6 with a6 | ⟨⟨T', k', p', b1, b2, b3, b4⟩, T'', k'', c1, c2, c3⟩
    · exact Or.inl a6
    · refine Or.inr ⟨⟨T', k', p', b1, b2, g8 T' k' p' b3, ?_⟩, T'', k'', c1, c2, g14 _ _ c3⟩
      exact agree_prefix_left (agree_prefix_right b4 (g4 T').1) ⟨X, hX⟩
  /- stage-3 proof:
  := by
  intro hg hae
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, -, -, -, -, -, g14⟩ := hg
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hae
  have hp := (g4 T).1
  obtain ⟨X, hX⟩ := hp
  refine ⟨?_, ?_, a3, ?_, ?_, ?_⟩
  · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp a1
    rw [g3 T ℓ hℓ]; simp
  · rw [← hX]; simp; omega
  · intro h1; rw [← hX, termAt_append_left _ _ _ (by omega)]; exact a4 h1
  · rw [← hX, List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp; omega)]
    exact a5
  · rcases a6 with a6 | ⟨⟨T', k', b1, b2, b3, b4⟩, T'', k'', c1, c2, c3⟩
    · exact Or.inl a6
    · refine Or.inr ⟨⟨T', k', b1, b2, g8 T' k' b3, ?_⟩, T'', k'', c1, c2, g14 _ _ c3⟩
      exact agree_prefix_left (agree_prefix_right b4 (g4 T').1) ⟨X, hX⟩
  -/

/-- A recorded commit stays committed (for `commit`'s precondition from earlier acknowledgements:
the acknowledgements only grow). -/
theorem committed_grows (σ σ' : PState) (T k p : Nat) :
    Grows σ σ' → committed σ T k p → committed σ' T k p := by
  intro hg hc
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, _⟩ := hg
  have hG : HG σ σ' := ⟨g1, g3, fun T => (g4 T).1, fun T hT => (g4 T).2 (Or.inl hT), g2.2⟩
  exact committed_grow hG g7 hc

/-! ### Applying: state-machine safety -/

/-- An entry in a server's durable prefix is the committed log's entry there. -/
theorem dur_C (σ : PState) (i : SID) (x : Nat) :
    PInv σ → i ∈ σ.srvs → 1 ≤ x → x ≤ (σ.srv i).dur.1 →
      x ≤ σ.C.length ∧ ent σ.C x = ent (σ.log i) x := by
  intro h hi hx1 hx2
  rcases (h.2.2.2.2.2.2.2.2.2.1 i hi).1 with hd | ⟨_, ⟨k', p', hk', hck⟩, hag⟩
  · omega
  · have hC := (h.2.2.2.2.2.2.2.2.1.1 _ _ _ hck).2.2
    have := hC.1
    refine ⟨by omega, ?_⟩
    rw [agree_ent hC (show x ≤ k' by omega), agree_ent hag hx2]
  /- stage-3 proof:
  := by
  intro h hi hx1 hx2
  rcases (h.2.2.2.2.2.2.2.2.2.1 i hi).1 with hd | ⟨_, ⟨k', hk', hck⟩, hag⟩
  · omega
  · have hC := (h.2.2.2.2.2.2.2.2.1.1 _ _ hck).2
    have := hC.1
    refine ⟨by omega, ?_⟩
    rw [agree_ent hC (show x ≤ k' by omega), agree_ent hag hx2]
  -/

/-- An entry of the committed log of term `t` is the leader log of `t`'s entry there. -/
theorem C_llog (σ : PState) (x : Nat) (e : Entry) :
    PInv σ → ent σ.C x = some e → ent (σ.llog e.term) x = some e := by
  intro h he
  have hl := ent_le_length he
  have a := h.2.2.1.2.2.2.1 x hl.1 hl.2
  rw [termAt_of_ent he] at a
  rw [← agree_ent a (Nat.le_refl _)]
  exact he

end proto
end github_com.hashicorp.raft
end Perennial
