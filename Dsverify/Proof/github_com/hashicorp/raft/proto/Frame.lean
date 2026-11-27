/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Frame.lean (241f27e).
-/
/-
`proto` — frame lemmas: conjuncts of `PInv` that survive any step growing the history in the
usual way (leaders only added, leader logs only extended, the election length of an existing
leader unchanged, logs only extended, terms only raised).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Cfg

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-- The history-growth hypotheses shared by the steps. -/
structure HG (σ σ' : PState) : Prop where
  srvs : σ'.srvs = σ.srvs
  leader : ∀ T ℓ, σ.leader T = some ℓ → σ'.leader T = some ℓ
  llog : ∀ T, σ.llog T <+: σ'.llog T
  len0 : ∀ T, σ.leader T ≠ none → σ'.len0 T = σ.len0 T
  /-- (stage 4) the configuration decoding is fixed. -/
  cv : σ'.cv = σ.cv

theorem HG.ne_none {σ σ' : PState} (hg : HG σ σ') {T : Nat} (h : σ.leader T ≠ none) :
    σ'.leader T ≠ none := by
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp h
  rw [hg.leader T ℓ hℓ]; simp

theorem HG.len {σ σ' : PState} (hg : HG σ σ') (T : Nat) : (σ.llog T).length ≤ (σ'.llog T).length :=
  (hg.llog T).length_le

theorem agree_of_prefix_both {A A' B B' : RLog} {k : Nat} (h : agree A' B' k) (hA : A <+: A')
    (hB : B <+: B') (hkA : k ≤ A.length) (hkB : k ≤ B.length) : agree A B k := by
  have a := agree_of_prefix hA hkA
  have b := agree_of_prefix hB hkB
  exact agree_trans (agree_trans a h) (agree_symm b)

theorem lacks_grow {σ σ' : PState} (hg : HG σ σ') (hL : ILeaders σ) {T'' k T : Nat}
    (h'' : σ.leader T'' ≠ none) (hk : k ≤ (σ.llog T).length) :
    lacks σ T'' k T → lacks σ' T'' k T := by
  intro hl ⟨h1, h2⟩
  apply hl
  rw [hg.len0 _ h''] at h1
  refine ⟨h1, ?_⟩
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp h''
  have := (hL.1 T'' ℓ hℓ).2.2.2.1
  exact agree_of_prefix_both h2 (hg.llog _) (hg.llog _) (by omega) hk

theorem IAcks_grow {σ σ' : PState} (hg : HG σ σ') (hL : ILeaders σ)
    (hlog : ∀ j ∈ σ.srvs, σ.log j <+: σ'.log j) (hterm : ∀ j ∈ σ.srvs, σ.term j ≤ σ'.term j)
    (hack : ∀ j T m, σ'.acked j T m → σ.acked j T m) (hA : IAcks σ) : IAcks σ' := by
  intro j T m ha
  obtain ⟨hj, hld, hm, hT, hk⟩ := hA j T m (hack _ _ _ ha)
  refine ⟨hg.srvs ▸ hj, hg.ne_none hld, Nat.le_trans hm (hg.len T),
    Nat.le_trans hT (hterm j hj), fun k hkm => ?_⟩
  rcases hk k hkm with h | ⟨T'', a, b, c, d⟩
  · exact Or.inl (agree_prefix_left (agree_prefix_right h (hg.llog T)) (hlog j hj))
  · exact Or.inr ⟨T'', a, Nat.le_trans b (hterm j hj), hg.ne_none c,
      lacks_grow hg hL c (Nat.le_trans hkm hm) d⟩

theorem IVoteAck_grow {σ σ' : PState} (hg : HG σ σ') (hL : ILeaders σ) (hA : IAcks σ)
    (hvote : ∀ j T x, σ'.votes j T = some x → σ.votes j T = some x)
    (hack : ∀ j T m, σ'.acked j T m → σ.acked j T m) (hVA : IVoteAck σ) : IVoteAck σ' := by
  intro j T' c L b T m k hv ha hkm hTT'
  have ha0 := hack _ _ _ ha
  have hm := (hA j T m ha0).2.2.1
  rcases hVA j T' c L b T m k (hvote _ _ _ hv) ha0 hkm hTT' with h | ⟨T'', a, b', c', d⟩
  · exact Or.inl (agree_prefix_right h (hg.llog T))
  · exact Or.inr ⟨T'', a, b', hg.ne_none c', lacks_grow hg hL c' (Nat.le_trans hkm hm) d⟩

theorem termAt_grow {A A' : RLog} {k : Nat} (hp : A <+: A') (hk : k ≤ A.length) :
    termAt A' k = termAt A k :=
  (agree_termAt (agree_of_prefix hp hk) (Nat.le_refl _)).symm

theorem committed_grow {σ σ' : PState} (hg : HG σ σ') (hack : ∀ j T m, σ.acked j T m → σ'.acked j T m)
    {T k p : Nat} (h : committed σ T k p) : committed σ' T k p := by
  obtain ⟨h1, h2, h3, h4, e, he, hk, Q, hQ, hQa⟩ := h
  refine ⟨hg.ne_none h1, h2, Nat.le_trans h3 (hg.len T), ?_, e, ?_, hk, Q, hg.cv ▸ hQ, ?_⟩
  · rw [termAt_grow (hg.llog T) h3]; exact h4
  · rw [← agree_ent (agree_of_prefix (hg.llog T) (ent_le_length he).2) (Nat.le_refl _)]; exact he
  · intro j hj
    obtain ⟨m, hm, ha⟩ := hQa j hj
    exact ⟨m, hm, hack _ _ _ ha⟩
  /- stage-3 proof:
  := by
  obtain ⟨h1, h2, h3, h4, Q, hQ, hQa⟩ := h
  refine ⟨hg.ne_none h1, h2, Nat.le_trans h3 (hg.len T), ?_, Q, isQuorum_congr hg.srvs hQ, ?_⟩
  · rw [termAt_grow (hg.llog T) h3]; exact h4
  · intro j hj
    obtain ⟨m, hm, ha⟩ := hQa j hj
    exact ⟨m, hm, hack _ _ _ ha⟩
  -/

theorem cfgAdmAt_grow {σ σ' : PState} (hg : HG σ σ') {T q p : Nat} (hl : σ.leader T ≠ none)
    (hq : q ≤ (σ.llog T).length) (h : cfgAdmAt σ T q p) : cfgAdmAt σ' T q p := by
  have e : (σ'.llog T).take q = (σ.llog T).take q := (agree_of_prefix (hg.llog T) hq).2.2.symm
  unfold cfgAdmAt
  rw [e, hg.len0 T hl]
  have : lastCfgIdx ((σ.llog T).take q) - 1 ≤ q := by have := lc_le (σ.llog T) q; omega
  have e2 : (σ'.llog T).take (lastCfgIdx ((σ.llog T).take q) - 1) =
      (σ.llog T).take (lastCfgIdx ((σ.llog T).take q) - 1) :=
    (agree_of_prefix (hg.llog T) (by omega)).2.2.symm
  rw [e2]; exact h

theorem cfgAdm_grow {σ σ' : PState} (hg : HG σ σ') {T k p : Nat} (hl : σ.leader T ≠ none)
    (h : cfgAdm σ T k p) : cfgAdm σ' T k p := by
  obtain ⟨q, h1, h2, h3⟩ := h
  exact ⟨q, h1, Nat.le_trans h2 (hg.len T), cfgAdmAt_grow hg hl h2 h3⟩

theorem ICommits_grow {σ σ' : PState} (hg : HG σ σ') (hack : ∀ j T m, σ.acked j T m → σ'.acked j T m)
    (hcom : ∀ T k p, σ'.commits T k p ↔ σ.commits T k p) (hC : σ'.C = σ.C) (h : ICommits σ) :
    ICommits σ' := by
  refine ⟨fun T k p hc => ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := h.1 T k p ((hcom T k p).mp hc)
    exact ⟨committed_grow hg hack a, cfgAdm_grow hg a.1 b, hC ▸ agree_prefix_right c (hg.llog T)⟩
  · rcases h.2 with h2 | ⟨T, p, hT⟩
    · exact Or.inl (hC ▸ h2)
    · exact Or.inr ⟨T, p, by rw [hcom, hC]; exact hT⟩
  /- stage-3 proof:
  := by
  refine ⟨fun T k hc => ?_, ?_⟩
  · obtain ⟨a, b⟩ := h.1 T k ((hcom T k).mp hc)
    exact ⟨committed_grow hg hack a, hC ▸ agree_prefix_right b (hg.llog T)⟩
  · rcases h.2 with h2 | ⟨T, hT⟩
    · exact Or.inl (hC ▸ h2)
    · exact Or.inr ⟨T, by rw [hcom, hC]; exact hT⟩
  -/

theorem IDur_grow {σ σ' : PState} (hg : HG σ σ')
    (hlog : ∀ j ∈ σ.srvs, σ.log j <+: σ'.log j) (hterm : ∀ j ∈ σ.srvs, σ.term j ≤ σ'.term j)
    (hdur : ∀ j ∈ σ.srvs, (σ'.srv j).dur = (σ.srv j).dur ∧ (σ'.srv j).cidx = (σ.srv j).cidx)
    (hcom : ∀ T k p, σ.commits T k p → σ'.commits T k p) (h : IDur σ) : IDur σ' := by
  intro i hi
  rw [hg.srvs] at hi
  obtain ⟨hd, hc⟩ := h i hi
  rw [(hdur i hi).1, (hdur i hi).2]
  refine ⟨?_, hc⟩
  rcases hd with hd | ⟨a, ⟨k', p, hk', hck⟩, b⟩
  · exact Or.inl hd
  · exact Or.inr ⟨Nat.le_trans a (hterm i hi), ⟨k', p, hk', hcom _ _ _ hck⟩,
      agree_prefix_left (agree_prefix_right b (hg.llog _)) (hlog i hi)⟩
  /- stage-3 proof:
  := by
  intro i hi
  rw [hg.srvs] at hi
  obtain ⟨hd, hc⟩ := h i hi
  rw [(hdur i hi).1, (hdur i hi).2]
  refine ⟨?_, hc⟩
  rcases hd with hd | ⟨a, ⟨k', hk', hck⟩, b⟩
  · exact Or.inl hd
  · exact Or.inr ⟨Nat.le_trans a (hterm i hi), ⟨k', hk', hcom _ _ hck⟩,
      agree_prefix_left (agree_prefix_right b (hg.llog _)) (hlog i hi)⟩
  -/

theorem HG.refl_llog {σ σ' : PState} (hv : σ'.srvs = σ.srvs) (hl : σ'.leader = σ.leader)
    (hll : σ'.llog = σ.llog) (hl0 : σ'.len0 = σ.len0) (hcv : σ'.cv = σ.cv) : HG σ σ' :=
  ⟨hv, fun T ℓ h => hl ▸ h, fun T => hll ▸ List.prefix_refl _, fun T _ => hl0 ▸ rfl, hcv⟩

/-- `IPub` survives a step that keeps the publications and the durable prefixes, grows the
leaders, the commits and the terms. -/
theorem IPub_grow {σ σ' : PState} (hg : HG σ σ') (hterm : ∀ j ∈ σ.srvs, σ.term j ≤ σ'.term j)
    (hdur : ∀ j ∈ σ.srvs, (σ'.srv j).dur.1 = (σ.srv j).dur.1)
    (hcom : ∀ T k p, σ.commits T k p → σ'.commits T k p) (hpub : σ'.pubs = σ.pubs) (h : IPub σ) :
    IPub σ' := by
  refine ⟨fun T k hp => ?_, fun i hi => ?_⟩
  · rw [hpub] at hp
    obtain ⟨a, k', p, hk, hc⟩ := h.1 T k hp
    exact ⟨hg.ne_none a, k', p, hk, hcom _ _ _ hc⟩
  · rw [hg.srvs] at hi
    rw [hdur i hi, hpub]
    rcases h.2 i hi with h0 | ⟨T, k, a, b, c⟩
    · exact Or.inl h0
    · exact Or.inr ⟨T, k, Nat.le_trans a (hterm i hi), b, c⟩
  /- stage-3 proof:
  := by
  refine ⟨fun T k hp => ?_, fun i hi => ?_⟩
  · rw [hpub] at hp
    obtain ⟨a, k', hk, hc⟩ := h.1 T k hp
    exact ⟨hg.ne_none a, k', hk, hcom _ _ hc⟩
  · rw [hg.srvs] at hi
    rw [hdur i hi, hpub]
    rcases h.2 i hi with h0 | ⟨T, k, a, b, c⟩
    · exact Or.inl h0
    · exact Or.inr ⟨T, k, Nat.le_trans a (hterm i hi), b, c⟩
  -/

/-- (stage 4) `ICfgR` survives a step that keeps the leaders, the leader logs, the election
lengths and the decoding, and only grows the recorded commits. -/
theorem ICfgR_frame {σ σ' : PState} (hl : σ'.leader = σ.leader) (hll : σ'.llog = σ.llog)
    (hl0 : σ'.len0 = σ.len0) (hcv : σ'.cv = σ.cv)
    (hcom : ∀ T k p, σ.commits T k p → σ'.commits T k p) (h : ICfgR σ) : ICfgR σ' := by
  intro T p e h1 h2 h3 h4
  rw [hl] at h1; rw [hl0] at h2; rw [hll] at h3
  obtain ⟨hadj, k, pc, q, hc, a, b, c, d, f⟩ := h T p e h1 h2 h3 h4
  refine ⟨?_, k, pc, q, hcom _ _ _ hc, by rw [hl0]; exact a, by rw [hll]; exact b, c, d, ?_⟩
  · simp only [cfgOf, hcv, hll]; exact hadj
  · unfold cfgAdmAt; rw [hll, hl0]; exact f

/-- (stage 4) `ICfgOk` survives a step that keeps the leader logs, the decoding and the servers. -/
theorem ICfgOk_frame {σ σ' : PState} (hll : σ'.llog = σ.llog) (hcv : σ'.cv = σ.cv)
    (hv : σ'.srvs = σ.srvs) (h : ICfgOk σ) : ICfgOk σ' := by
  intro T k e he hk
  rw [hll] at he
  rw [hcv, hv]; exact h T k e he hk

/-- (stage 4) `cfgAdmAt` depends only on the leader log and election length of its term. -/
theorem cfgAdmAt_congr {σ σ' : PState} {T q p : Nat} (hll : σ'.llog T = σ.llog T)
    (hl0 : σ'.len0 T = σ.len0 T) : cfgAdmAt σ' T q p ↔ cfgAdmAt σ T q p := by
  unfold cfgAdmAt; rw [hll, hl0]

end proto
end github_com.hashicorp.raft
end Perennial
