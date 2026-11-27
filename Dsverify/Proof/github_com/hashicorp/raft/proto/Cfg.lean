/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Cfg.lean (241f27e).
-/
/-
`proto` (stage 4) — configurations: the configuration lemma `CL0` (the heart of membership
changes), quorum meeting for adjacent configurations, and the laws the code uses about
configurations (`notes/stage4-plan.md`, A3 and A6).

**Why `CL0`.** With a fixed voter set any two quorums meet; with configurations read from logs, the
election quorum of a new leader (a quorum of the latest configuration of its log `L`) and the
quorum that committed a prefix (a quorum of the configuration the commitment counted, `p` in
`llog T`) are of different configurations. `CL0` says: if `L` lacks `llog T [1..q]`, either the two
configurations' quorums meet, or there is a recorded commit `L` lacks whose configuration's quorums
meet `L`'s. Its uses: leader completeness at an election (`becomeLeader`), at a commit or an
acknowledgement (`ILC` when a quorum completes), at `leaderAppendCfg` (`ILC` for the newly admissible
`(T, k, p)`, review tier-2 1), election safety (`elect_safety`, review tier-2 1), and the read bound
(`Read.lean`).

**Paper proof** (A3). `d` := the longest common prefix of `L` and `llog T` (`d < q`). `P` := the
last configuration at `≤ d` (common). `f₁ < f₂ < …` the configurations of `llog T` in `(d, q]`,
`g₁ < … < g_s` those of `L` in `(d, |L|]`. Each `x` of these was appended by the leader of its term
`T_x` (`p_x > len0 T_x`) and has, by `ICfgR`, its R-commit `(T_x, k_x, pc_x)` with
`p(par x) ≤ k_x < p_x`, `k_x > len0 T_x` and `pc_x` admissible (`par x`, or `par (par x)` when
`par x` is `T_x`'s own). Terms of `L` are `≤ T`; `llog T`'s too.
* `L` has no configuration after `d`: `cfgOf L = P`. If `pM`'s configuration is `P`: equal. If it
  is `f₁` (or the window's `f₁`, parent of `f₂`): adjacent (`P = par f₁`). Otherwise `f₂` exists,
  its R-commit counts with `f₁` or `P` (adjacent / equal to `P`), has `k ≥ p(f₁) > d`: `L` lacks
  it; `T_{f₂} ≤ T`. (Window with `P` itself `T`'s own entry at `≤ d`: then `lastTerm L = T`, `L` is
  a prefix of `llog T`, `cfgOf L = P` and `pM = par P`: adjacent.)
* `L` has `g₁..g_s` after `d` and `llog T` none in `(d, q]`: `pM`'s configuration is `P` (or
  `par P`, which forces `L` to be a prefix of `llog T`: impossible with `g₁` after `d`). `s = 1`:
  `g₁` adjacent to `P`. `s ≥ 2`: `T_{g₂} ≤ T`; `T_{g₂} = T` puts `g₂` in `llog T` (contradiction
  with `d`); `T_{g₂} < T`: the leader of `T` contains `g₂`'s R-commit (hypothesis), which holds
  `g₁` (`k ≥ p(g₁) > d`): contradiction.
* Both have configurations after `d` (`f₁`, `g₁`, both children of `P`, `T_{f₁} ≠ T_{g₁}` by `d`):
  - `T_{g₁} < T_{f₁}`: the leader of `T_{f₁}` contains `g₁`'s R-commit, so `d ≥ k_{g₁}`; `P` is not
    `T_{f₁}`'s own (it is in `llog T_{g₁}`, terms `≤ T_{g₁}`): `f₁`'s R-commit counts with `P` and
    has `k > d` (the entry at `d+1` of `llog T` has a term `> T_{g₁}`, by term monotonicity and log
    matching, so `len0 T_{f₁} ≥ d`): `L` lacks it. `s = 1`: adjacent (`g₁`, `P`). `s ≥ 2`:
    `T_{g₂}` vs `T_{f₁}`: `<` puts `g₁` in `llog T` (via the leader of `T_{f₁}` containing `g₂`'s
    R-commit), `>` puts `llog T[d+1]` in `L` (via the leader of `T_{g₂}` containing `f₁`'s
    R-commit): both contradict `d`.
  - `T_{g₁} > T_{f₁}`: then `T_{g₁} < T` (`= T` puts `g₁` in `llog T`), the leader of `T` contains
    `g₁`'s R-commit, whose last entry (term `T_{g₁}`) is at `k_{g₁} ≤ d`; but `llog T[d+1]` has
    term `≤ T_{f₁} < T_{g₁}`: terms decrease along `llog T`, contradiction.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.CL0

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ## Configurations of a log -/

/-- `lastCfgIdx L` is `0` or the index of a configuration entry of `L`, and no later entry of `L`
is a configuration. -/
theorem lastCfgIdx_spec (L : RLog) :
    lastCfgIdx L ≤ L.length ∧
    (lastCfgIdx L = 0 ∨ ∃ e, ent L (lastCfgIdx L) = some e ∧ e.kind = kConfig) ∧
    ∀ k e, lastCfgIdx L < k → ent L k = some e → e.kind ≠ kConfig := by
  obtain ⟨a, b, c⟩ := lastCfgIdx_isLast L
  refine ⟨a, ?_, ?_⟩
  · rcases b with b | b
    · exact Or.inl b
    · exact Or.inr ((isCfgAt_iff _ _).mp b)
  · intro k e hk he
    exact (isCfgAt_false_iff _ _).mp (c k hk (ent_le_length he).2) e he

/-- Appending entries that are not configurations keeps the latest configuration. -/
theorem lastCfgIdx_append_noCfg (L es : RLog) (h : ∀ e ∈ es, e.kind ≠ kConfig) :
    lastCfgIdx (L ++ es) = lastCfgIdx L := by
  apply lastCfgIdx_eq_of_isLast
  have hl := lastCfgIdx_le L
  have hleft : ∀ k, k ≤ L.length → isCfgAt (L ++ es) k = isCfgAt L k := fun k hk => by
    simp [isCfgAt, ent_append_left L es k hk]
  refine ⟨by simp; omega, ?_, fun k h1 h2 => ?_⟩
  · rcases lastCfgIdx_cfg L with h | h
    · exact Or.inl h
    · rw [hleft _ hl]; exact Or.inr h
  · by_cases hk : k ≤ L.length
    · rw [hleft k hk]; exact (lastCfgIdx_isLast L).2.2 k h1 hk
    · rw [isCfgAt_false_iff]
      intro e he
      rw [ent_append_right L es k (by omega)] at he
      unfold ent at he
      split at he
      · cases he
      · exact h e (List.mem_of_getElem? he)

/-- Appending a configuration entry makes it the latest. -/
theorem lastCfgIdx_append_cfg (L : RLog) (e : Entry) (h : e.kind = kConfig) :
    lastCfgIdx (L ++ [e]) = L.length + 1 := by
  apply lastCfgIdx_eq_of_isLast
  refine ⟨by simp, Or.inr ?_, fun k h1 h2 => by simp at h2; omega⟩
  rw [isCfgAt_iff]
  refine ⟨e, ?_, h⟩
  rw [ent_append_right L [e] _ (by omega)]
  simp [ent]

/-- The latest configuration of a prefix through index `x` depends only on that prefix. -/
theorem lastCfgIdx_agree (A B : RLog) (x : Nat) (h : agree A B x) :
    lastCfgIdx (A.take x) = lastCfgIdx (B.take x) := by
  exact lc_take_of_agree h

/-! ## Quorums of adjacent configurations meet -/

/-- **Quorum meeting** (single-server changes): two configurations equal as sets or adjacent
(`adjV`: one server added or removed) have meeting quorums. With `|B| = |A| + 1`: a quorum of `B`
keeps at least `⌊(|A|+1)/2⌋` members in `A`, a quorum of `A` has at least `⌊|A|/2⌋ + 1`: together
more than `|A|`. -/
theorem quorum_meet {A B Q1 Q2 : List SID} (hA : A.Nodup) (hB : B.Nodup)
    (hAB : (∀ y, y ∈ A ↔ y ∈ B) ∨ adjV A B) (h1 : isQuorumOf A Q1) (h2 : isQuorumOf B Q2) :
    ∃ j, j ∈ Q1 ∧ j ∈ Q2 := by
  exact cfgMeet_of_adj' hA hB hAB Q1 Q2 h1 h2

/-- `quorum_meet` as `cfgMeet`. -/
theorem cfgMeet_of_adj {A B : List SID} (hA : A.Nodup) (hB : B.Nodup)
    (hAB : (∀ y, y ∈ A ↔ y ∈ B) ∨ adjV A B) : cfgMeet A B := by
  exact cfgMeet_of_adj' hA hB hAB

/-! ## The configuration lemma -/

/-- **CL0** (A3). Hypotheses, from `PInv` restricted below a term `T''`: the shapes (`IGen`,
`ILeaders`), log matching for every history log (`ILogs`), the R-commits (`ICfgR`), recorded commits
committed by an admissible configuration (`ICommits`' first part, without `C`), and leader
completeness for every leader of a term `T' < T''` (no such leader lacks a prefix committed by an
admissible configuration of a term `< T'`). Let `L` be a history log (`LMok`) with
`lastTerm L ≤ T < T''`, `T` with a leader, `q ≤ |llog T|`, `pM` admissible for `q`, and `L` not
agreeing with `llog T` up to `q`. Then the latest configuration of `L` meets the configuration at
`pM`, or there is a recorded commit `(T*, k*, p*)` with `T* ≤ T` that `L` lacks and whose
configuration meets `L`'s. (Paper proof: the module doc.) -/
theorem CL0 (σ : PState) (T'' : Nat) (hG : IGen σ) (hL : ILeaders σ) (hLo : ILogs σ)
    (hR : ICfgR σ)
    (hCo : ∀ T k p, σ.commits T k p → committed σ T k p ∧ cfgAdm σ T k p)
    (hLC : ∀ T k p, committed σ T k p → cfgAdm σ T k p →
      ∀ T', T < T' → T' < T'' → σ.leader T' ≠ none → ¬ lacks σ T' k T)
    (L : RLog) (hLM : LMok σ L) (T q pM : Nat) (hT : lastTerm L ≤ T) (hT'' : T < T'')
    (hl : σ.leader T ≠ none) (hq : q ≤ (σ.llog T).length) (hpM : cfgAdmAt σ T q pM)
    (hna : ¬ (q ≤ L.length ∧ agree L (σ.llog T) q)) :
    cfgMeet (cfgOf σ L) (cfgAt σ (σ.llog T) pM) ∨
    ∃ T' k' p', σ.commits T' k' p' ∧ T' ≤ T ∧ ¬ (k' ≤ L.length ∧ agree L (σ.llog T') k') ∧
      cfgMeet (cfgOf σ L) (cfgAt σ (σ.llog T') p') := by
  exact CL0' σ T'' hG hL hLo hR hCo hLC L hLM T q pM hT hT'' hl hq hpM hna

/-- **Election safety with configurations** (review tier-2 1; the pure content of
`gprot.leader_votes_agree`): a candidate `c` of `T` whose election log `L` (a history log, its last
entry `c`'s recorded one) has a quorum `Q` of `L`'s configuration voting for it in `T` is the leader
`ℓ` of `T`, if `T` has one. Paper proof: the two election logs (`L` and `ℓ`'s,
`(σ.llog T).take (σ.len0 T)`); `CL0` with the one of the smaller last term as its `L`, `T :=` the
other's last term, `q :=` the other's length, `T'' := T` (its hypotheses are `PInv`'s below `T`).
If they agree up to `q`, one extends the other by entries of its last term: at most one
configuration entry after the common prefix (the R-commit of a second one would be a commit of that
term, covering the first, against `ILC`), so the two configurations are equal or adjacent
(`quorum_meet`). If `CL0` gives a recorded commit `(T*, k*, p*)` the log lacks whose configuration
meets its own, a common voter acknowledged `k*` in `T*` and voted in `T > T*` with a log lacking it:
`IVoteAck`'s late-vote branch gives a leader of `T'' ∈ (T*, T]` lacking it, against `ILC` (for
`T'' = T`, on the existing leader `ℓ`). Otherwise the quorums meet: a common voter voted for both,
once (`IVotes`). -/
theorem elect_safety (σ : PState) (hP : PInv σ) (T : Nat) (ℓ c : SID) (L : RLog) (Q : List SID)
    (hl : σ.leader T = some ℓ) (hLM : LMok σ L)
    (hc : σ.cand c T = some (L.length, lastTerm L)) (hQ : isQuorumOf (cfgOf σ L) Q)
    (hv : ∀ j ∈ Q, ∃ L' b, σ.votes j T = some (c, L', b)) : ℓ = c := by
  have hlt : lastTerm L < T := (hP.2.2.2.2.1.2.2 c T _ hc).2.2.2.2
  exact elect_safety_lt σ hP T ℓ c L Q hl hLM hlt hc hQ hv

/-! ## Laws for the code (A6) -/

/-- The leader of its current term: its latest configuration is the leader log's. -/
theorem leader_cfgOf (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → σ.leader (σ.term i) = some i →
      lastCfgIdx (σ.log i) = lastCfgIdx (σ.llog (σ.term i)) ∧
      cfgOf σ (σ.log i) = cfgOf σ (σ.llog (σ.term i)) := by
  intro hP hi hl
  rw [hP.2.2.2.1 i hi hl]
  exact ⟨rfl, rfl⟩

/-- **The committed parent** (`cfg_prev_committed`; `processConfigurationLogEntry` makes the previous
latest configuration the committed one): a configuration entry at `p` of a server's log whose
previous configuration is at `p' > 0` has that previous entry in the committed log (its R-commit
covers `p'`, `ICfgR`, and is in `C`, `ICommits`). -/
theorem cfg_prev_committed (σ : PState) (i : SID) (p : Nat) (e : Entry) :
    PInv σ → i ∈ σ.srvs → ent (σ.log i) p = some e → e.kind = kConfig →
      0 < lastCfgIdx ((σ.log i).take (p - 1)) →
      lastCfgIdx ((σ.log i).take (p - 1)) ≤ σ.C.length ∧
      ent σ.C (lastCfgIdx ((σ.log i).take (p - 1))) =
        ent (σ.log i) (lastCfgIdx ((σ.log i).take (p - 1))) := by
  intro hP hi he hk hpar
  obtain ⟨hG, hL, hLo, _, _, _, _, _, hCm, _, _, _, _, hR⟩ := hP
  have hM : LMok σ (σ.log i) := (hLo.1 i hi).1
  have hpc : isCfgAt (σ.log i) p = true := (isCfgAt_iff _ _).mpr ⟨e, he, hk⟩
  have hp2 : 2 ≤ p := by have := lc_le (σ.log i) (p - 1); omega
  obtain ⟨_, _, _, _, a, _, _, _, k, pc, q, hc, _, hk2, hk3, hk4, _⟩ := cfgR_hist hG hL hLo hR hM hpc hp2
  have hC := (hCm.1 _ _ _ hc).2.2
  have hag : agree σ.C (σ.log i) k := agree_trans hC (agree_symm (agree_mono a (by omega)))
  exact ⟨by have := hag.1; omega, agree_ent hag hk2⟩

/-- **The snapshot's configuration** (`snap_cfg`): within a server's durable prefix, its log's
latest configuration at or below `x` is the committed log's. -/
theorem snap_cfg (σ : PState) (i : SID) (x : Nat) :
    PInv σ → i ∈ σ.srvs → x ≤ (σ.srv i).dur.1 →
      x ≤ σ.C.length ∧ lastCfgIdx (σ.C.take x) = lastCfgIdx ((σ.log i).take x) ∧
      cfgOf σ (σ.C.take x) = cfgOf σ ((σ.log i).take x) := by
  intro hP hi hx
  obtain ⟨hG, hL, hLo, _, _, _, _, _, hCm, hD, _, _, _, hR⟩ := hP
  have hag : agree σ.C (σ.log i) x := by
    rcases (hD i hi).1 with h0 | ⟨_, ⟨k', p, hk', hc⟩, a⟩
    · rw [h0] at hx; have : x = 0 := by omega
      subst this; exact agree_zero _ _
    · have hC := (hCm.1 _ _ _ hc).2.2
      exact agree_mono (agree_trans (agree_mono hC hk') (agree_symm a)) hx
  refine ⟨hag.1, ?_, ?_⟩ <;> rw [hag.2.2]

/-- A server's latest configuration, when it has one, is valid over the servers (`ICfgOk`). -/
theorem log_cfgOf_valid (σ : PState) (i : SID) :
    PInv σ → i ∈ σ.srvs → 0 < lastCfgIdx (σ.log i) → cfgValid σ.srvs (cfgOf σ (σ.log i)) := by
  intro hP hi h0
  obtain ⟨hG, hL, hLo, _⟩ := hP
  have hc : isCfgAt (σ.log i) (lastCfgIdx (σ.log i)) = true := by
    rcases lastCfgIdx_cfg (σ.log i) with h | h
    · omega
    · exact h
  exact cfgAt_valid hG hL hLo (hLo.1 i hi).1 hc

end proto
end github_com.hashicorp.raft
end Perennial
