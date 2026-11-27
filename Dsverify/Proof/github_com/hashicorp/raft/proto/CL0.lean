/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/CL0.lean (241f27e).
-/
/-
`proto` (stage 4, internal) — the proof of the configuration lemma `CL0` (`Cfg.lean`), following
the paper proof of `notes/stage4-plan.md` A3 (module doc of `Cfg.lean`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.CfgLib

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

theorem CL0' (σ : PState) (T'' : Nat) (hG : IGen σ) (hL : ILeaders σ) (hLo : ILogs σ)
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
  -- the empty log has no configuration
  by_cases hL0 : L = []
  · subst hL0; rw [cfgOf_nil]; exact Or.inl (cfgMeet_nil_left _)
  have hLne : 1 ≤ L.length := by
    cases L with
    | nil => exact absurd rfl hL0
    | cons _ _ => simp
  have hLtM : LMok σ (σ.llog T) := hLo.2.1 T
  obtain ⟨ℓT, hℓT⟩ := Option.ne_none_iff_exists'.mp hl
  have hLT := hL.1 T ℓT hℓT
  have hLt1 : 1 ≤ (σ.llog T).length := by have := hLT.2.2.1; have := hLT.2.2.2.1; omega
  have hag1 : agree L (σ.llog T) 1 :=
    agree_of_ent hLne hLt1 (fun x h1 h2 => by
      have : x = 1 := by omega
      subst this
      rw [ent_one_g hG hL hLM hLne, hLT.2.2.2.2.1])
  -- `d`: the longest common prefix
  have hnq : ¬ agree L (σ.llog T) q := fun h => hna ⟨h.1, h⟩
  obtain ⟨n0, hn0, hn0min⟩ := exists_least (P := fun n => ¬ agree L (σ.llog T) n) ⟨q, hnq⟩
  have hn01 : 2 ≤ n0 := by
    apply Classical.byContradiction; intro h
    rcases (by omega : n0 = 0 ∨ n0 = 1) with h | h
    · subst h; exact hn0 (agree_zero _ _)
    · subst h; exact hn0 hag1
  have hn0q : n0 ≤ q := by
    apply Classical.byContradiction; intro h
    exact hn0min q (by omega) hnq
  have hd_ag : agree L (σ.llog T) (n0 - 1) :=
    Classical.not_not.mp (hn0min (n0 - 1) (by omega))
  have hd_max : ∀ n, agree L (σ.llog T) n → n ≤ n0 - 1 := by
    intro n hn
    apply Classical.byContradiction; intro h
    exact hn0 (agree_mono hn (by omega))
  generalize hd : n0 - 1 = d at hd_ag hd_max
  have hd1 : 1 ≤ d := by omega
  have hdq : d < q := by omega
  have hdL : d ≤ L.length := hd_ag.1
  have hdLt : d ≤ (σ.llog T).length := hd_ag.2.1
  clear hn0 hn0min hn01 hn0q hd hag1
  have hcon : ∀ n, agree L (σ.llog T) n → d < n → False := fun n h h' => by
    have := hd_max n h; omega
  have hvia : ∀ t n, agree L (σ.llog t) n → agree (σ.llog T) (σ.llog t) n → d < n → False :=
    fun t n a b h => hcon n (agree_trans a (agree_symm b)) h
  -- terms
  have hLterm : ∀ x, 1 ≤ x → x ≤ L.length → termAt L x ≤ T := fun x h1 h2 =>
    Nat.le_trans (LMok_le_last hG hL hLM h1 h2) hT
  have hLtterm : ∀ x, 1 ≤ x → x ≤ (σ.llog T).length → termAt (σ.llog T) x ≤ T :=
    fun x h1 h2 => llog_term_le hG hL h1 h2
  -- `P`, the common latest configuration at `d`
  have hP : lastCfgIdx (L.take d) = lastCfgIdx ((σ.llog T).take d) := lc_take_of_agree hd_ag
  obtain ⟨P, hPdef⟩ : ∃ P, lastCfgIdx ((σ.llog T).take d) = P := ⟨_, rfl⟩
  rw [hPdef] at hP
  have hPd : P ≤ d := hPdef ▸ lc_le _ d
  have hPL : cfgAt σ L P = cfgAt σ (σ.llog T) P := cfgAt_agree σ hd_ag hPd
  -- `pM` is `0` or a configuration of `llog T`, at most `q`
  have hpMq : pM ≤ q ∧ (pM = 0 ∨ isCfgAt (σ.llog T) pM = true) := by
    rcases hpM with h | ⟨h1, h⟩
    · subst h; exact ⟨lc_le _ q, lc_cfg _ q⟩
    · subst h
      have := lc_le (σ.llog T) q
      have := lc_le (σ.llog T) (lastCfgIdx ((σ.llog T).take q) - 1)
      exact ⟨by omega, lc_cfg _ _⟩
  have hlen0T : 1 ≤ σ.len0 T := hLT.2.2.1
  by_cases hA : ∀ k, d < k → k ≤ L.length → isCfgAt L k = false
  · ---------------- case A: no configuration of `L` after `d`
    have hG' : lastCfgIdx L = P := by rw [lastCfgIdx_eq_lc hdL hA, hP]
    have hcfgL : cfgOf σ L = cfgAt σ (σ.llog T) P := by
      show cfgAt σ L (lastCfgIdx L) = _
      rw [hG', hPL]
    rw [hcfgL]
    by_cases hpd : pM ≤ d
    · left
      rcases hpM with h | ⟨h1, h⟩
      · have e := lc_between (L := σ.llog T) (by omega : d ≤ q) hq (h ▸ hpd)
        rw [hPdef] at e
        rw [h, ← e]
        exact cfgMeet_refl _
      · by_cases hm : lastCfgIdx ((σ.llog T).take q) ≤ d
        · have e := lc_between (L := σ.llog T) (by omega : d ≤ q) hq hm
          rw [hPdef] at e
          rw [← e] at h h1
          have hPc : isCfgAt (σ.llog T) P = true := by
            rcases lc_cfg (σ.llog T) d with h0 | h0
            · omega
            · rw [hPdef] at h0; exact h0
          obtain ⟨_, _, _, _, _, _, _, hmeet, _⟩ :=
            cfgR_hist hG hL hLo hR hLtM hPc (by omega)
          rw [h]
          exact cfgMeet_symm hmeet
        · have hmq := lc_le (σ.llog T) q
          have e := lc_between (L := σ.llog T) (a := d) (b := lastCfgIdx ((σ.llog T).take q) - 1)
            (by omega) (by omega) (h ▸ hpd)
          rw [hPdef] at e
          rw [h, ← e]
          exact cfgMeet_refl _
    · have hpc : isCfgAt (σ.llog T) pM = true := by
        rcases hpMq.2 with h | h
        · omega
        · exact h
      obtain ⟨f1, hf1d, hf1q, hf1c, hf1m⟩ := first_cfg (X := σ.llog T) (a := d) (b := q) ⟨pM, by omega, hpMq.1, hpc⟩
      have hpf1 : lastCfgIdx ((σ.llog T).take (f1 - 1)) = P := by
        rw [← hPdef]; exact (lc_noCfg (by omega) (by omega) (fun k h1 h2 => hf1m k h1 (by omega))).symm
      obtain ⟨_, _, _, _, _, _, _, hmeet1, _⟩ := cfgR_hist hG hL hLo hR hLtM hf1c (by omega)
      rw [hpf1] at hmeet1
      have hf1p : f1 ≤ pM := by
        apply Classical.byContradiction; intro h
        rw [hf1m pM (by omega) (by omega)] at hpc; cases hpc
      by_cases he : pM = f1
      · left; rw [he]; exact hmeet1
      · obtain ⟨f2, hf2d, hf2q, hf2c, hf2m⟩ :=
          first_cfg (X := σ.llog T) (a := f1) (b := q) ⟨pM, by omega, hpMq.1, hpc⟩
        have hpf2 : lastCfgIdx ((σ.llog T).take (f2 - 1)) = f1 := by
          rw [← lc_self (L := σ.llog T) (by omega) hf1c]
          exact (lc_noCfg (by omega) (by omega) (fun k h1 h2 => hf2m k h1 (by omega))).symm
        obtain ⟨e2, _, _, hl2, a2, _, _, _, k2, pc2, q2, hc2, _, hk2a, hk2b, hk2c, hpc2⟩ :=
          cfgR_hist hG hL hLo hR hLtM hf2c (by omega)
        have hch := pc_char a2 hk2a hk2b hk2c hpc2
        rw [hpf2, hpf1] at hch
        rw [hpf2] at hk2a
        right
        refine ⟨_, k2, pc2, hc2, hLtterm f2 (by omega) (by have := a2.1; omega), ?_, ?_⟩
        · intro ⟨_, hag⟩
          exact hvia _ k2 hag (agree_mono a2 (by omega)) (by omega)
        · have hpc2le : pc2 ≤ f2 := by rcases hch with h | ⟨_, h⟩ <;> omega
          rw [cfgAt_agree σ (agree_symm a2) hpc2le]
          rcases hch with h | ⟨_, h⟩
          · rw [h]; exact hmeet1
          · rw [h]; exact cfgMeet_refl _
  · ---------------- case B: a configuration of `L` after `d`
    have hex : ∃ k, d < k ∧ k ≤ L.length ∧ isCfgAt L k = true := by
      apply Classical.byContradiction; intro hn
      apply hA; intro k h1 h2
      cases hc : isCfgAt L k
      · rfl
      · exact absurd ⟨k, h1, h2, hc⟩ hn
    obtain ⟨g1, hg1d, hg1L, hg1c, hg1m⟩ := first_cfg hex
    have hpg1 : lastCfgIdx (L.take (g1 - 1)) = P := by
      rw [← hP]; exact (lc_noCfg (by omega) (by omega) (fun k h1 h2 => hg1m k h1 (by omega))).symm
    obtain ⟨eg, _, _, hlg, ag, hg0, _, hmeetg, kg, pcg, qg, hcg, hkg0, hkga, hkgb, hkgc, hpcg⟩ :=
      cfgR_hist hG hL hLo hR hLM hg1c (by omega)
    rw [hpg1, hPL] at hmeetg
    rw [hpg1] at hkga
    have meetG : lastCfgIdx L = g1 → cfgMeet (cfgOf σ L) (cfgAt σ (σ.llog T) P) := by
      intro h
      show cfgMeet (cfgAt σ L (lastCfgIdx L)) _
      rw [h]; exact cfgMeet_symm hmeetg
    have hg2 : lastCfgIdx L ≠ g1 → ∃ g2 k2 pc2, g1 < g2 ∧ g2 ≤ L.length ∧
        σ.leader (termAt L g2) ≠ none ∧ agree L (σ.llog (termAt L g2)) g2 ∧
        σ.commits (termAt L g2) k2 pc2 ∧ g1 ≤ k2 ∧ k2 < g2 := by
      intro hne
      obtain ⟨x1, x2, x3⟩ := lastCfgIdx_isLast L
      have hge : g1 ≤ lastCfgIdx L := by
        apply Classical.byContradiction; intro h
        rw [x3 g1 (by omega) hg1L] at hg1c; cases hg1c
      have hlc : isCfgAt L (lastCfgIdx L) = true := by
        rcases x2 with h | h
        · omega
        · exact h
      obtain ⟨g2, hg2d, hg2L, hg2c, hg2m⟩ :=
        first_cfg (X := L) (a := g1) (b := L.length) ⟨lastCfgIdx L, by omega, x1, hlc⟩
      have hpg2 : lastCfgIdx (L.take (g2 - 1)) = g1 := by
        rw [← lc_self (L := L) (by omega) hg1c]
        exact (lc_noCfg (by omega) (by omega) (fun k h1 h2 => hg2m k h1 (by omega))).symm
      obtain ⟨_, _, _, hl2, a2, _, _, _, k2, pc2, q2, hc2, _, hk2a, hk2b, hk2c, _⟩ :=
        cfgR_hist hG hL hLo hR hLM hg2c (by omega)
      rw [hpg2] at hk2a
      exact ⟨g2, k2, pc2, hg2d, hg2L, hl2, a2, hc2, hk2a, by omega⟩
    by_cases hB1 : ∀ k, d < k → k ≤ q → isCfgAt (σ.llog T) k = false
    · -------- B1: no configuration of `llog T` in `(d, q]`
      have hm : lastCfgIdx ((σ.llog T).take q) = P := by
        rw [← hPdef]; exact (lc_noCfg (by omega) hq hB1).symm
      have hpMP : pM = P := by
        rcases hpM with h | ⟨h1, h⟩
        · rw [h, hm]
        · exfalso
          rw [hm] at h1
          have t1 : termAt (σ.llog T) P = T := own_term hL hl h1 (by omega)
          have t2 : termAt L P = T := by rw [agree_termAt hd_ag hPd]; exact t1
          have t3 := LMok_term_mono hG hL hLM (by omega : 1 ≤ P) (by omega : P ≤ g1) hg1L
          have t4 := hLterm g1 (by omega) hg1L
          have : termAt L g1 = T := by omega
          rw [this] at ag
          exact hcon g1 ag hg1d
      left
      rw [hpMP]
      by_cases hlg1 : lastCfgIdx L = g1
      · exact meetG hlg1
      · exfalso
        obtain ⟨g2, k2, pc2, hg12, hg2L, hl2, a2, hc2, hk2a, hk2b⟩ := hg2 hlg1
        have t4 := hLterm g2 (by omega) hg2L
        rcases Nat.lt_or_eq_of_le t4 with hlt | heq
        · have hnl := hLC _ k2 pc2 (hCo _ _ _ hc2).1 (hCo _ _ _ hc2).2 T hlt hT'' hl
          unfold lacks at hnl
          obtain ⟨_, hag⟩ := Classical.not_not.mp hnl
          exact hvia _ k2 (agree_mono a2 (by omega)) hag (by omega)
        · rw [heq] at a2
          exact hcon g2 a2 (by omega)
    · -------- B2: a configuration of `llog T` in `(d, q]`
      have hexf : ∃ k, d < k ∧ k ≤ q ∧ isCfgAt (σ.llog T) k = true := by
        apply Classical.byContradiction; intro hn
        apply hB1; intro k h1 h2
        cases hc : isCfgAt (σ.llog T) k
        · rfl
        · exact absurd ⟨k, h1, h2, hc⟩ hn
      obtain ⟨f1, hf1d, hf1q, hf1c, hf1m⟩ := first_cfg hexf
      have hpf1 : lastCfgIdx ((σ.llog T).take (f1 - 1)) = P := by
        rw [← hPdef]; exact (lc_noCfg (by omega) (by omega) (fun k h1 h2 => hf1m k h1 (by omega))).symm
      obtain ⟨ef, _, _, hlf, af, hf0, _, _, kf, pcf, qf, hcf, hkf0, hkfa, hkfb, hkfc, hpcf⟩ :=
        cfgR_hist hG hL hLo hR hLtM hf1c (by omega)
      have hchf := pc_char af hkfa hkfb hkfc hpcf
      rw [hpf1] at hchf hkfa
      have hf1len : f1 ≤ (σ.llog T).length := by omega
      have hf1lf : f1 ≤ (σ.llog (termAt (σ.llog T) f1)).length := af.2.1
      have hg1lg : g1 ≤ (σ.llog (termAt L g1)).length := ag.2.1
      rcases Nat.lt_trichotomy (termAt L g1) (termAt (σ.llog T) f1) with hlt | heq | hgt
      · -- `T_{g1} < T_{f1}`: `f1`'s R-commit counts with `P` and `L` lacks it
        have hpcfP : pcf = P := by
          rcases hchf with h | ⟨h1, h⟩
          · exact h
          · exfalso
            have t1 : termAt (σ.llog (termAt (σ.llog T) f1)) P = termAt (σ.llog T) f1 :=
              own_term hL hlf h1 (by omega)
            have t2 : termAt L P = termAt (σ.llog T) f1 := by
              rw [agree_termAt hd_ag hPd, agree_termAt af (by omega)]; exact t1
            have t3 := LMok_term_mono hG hL hLM (by omega : 1 ≤ P) (by omega : P ≤ g1) hg1L
            omega
        have hkfd : d < kf := by
          apply Classical.byContradiction; intro h
          have t1 : termAt (σ.llog (termAt (σ.llog T) f1)) d = termAt (σ.llog T) f1 :=
            own_term hL hlf (by omega) (by omega)
          have t2 : termAt L d = termAt (σ.llog T) f1 := by
            rw [agree_termAt hd_ag (Nat.le_refl _), agree_termAt af (by omega)]; exact t1
          have t3 := LMok_term_mono hG hL hLM hd1 (by omega : d ≤ g1) hg1L
          omega
        have lacksF : ¬ (kf ≤ L.length ∧ agree L (σ.llog (termAt (σ.llog T) f1)) kf) := by
          intro ⟨_, hag⟩
          exact hvia _ kf hag (agree_mono af (by omega)) hkfd
        right
        refine ⟨_, kf, pcf, hcf, hLtterm f1 (by omega) hf1len, lacksF, ?_⟩
        rw [cfgAt_agree σ (agree_symm af) (by omega : pcf ≤ f1), hpcfP]
        by_cases hlg1 : lastCfgIdx L = g1
        · exact meetG hlg1
        · exfalso
          obtain ⟨g2, k2, pc2, hg12, hg2L, hl2, a2, hc2, hk2a, hk2b⟩ := hg2 hlg1
          have t4 := hLterm g2 (by omega) hg2L
          rcases Nat.lt_trichotomy (termAt L g2) (termAt (σ.llog T) f1) with hlt2 | heq2 | hgt2
          · have hnl := hLC _ k2 pc2 (hCo _ _ _ hc2).1 (hCo _ _ _ hc2).2 _ hlt2
              (by have := hLtterm f1 (by omega) hf1len; omega) hlf
            unfold lacks at hnl
            obtain ⟨hk2l, hag⟩ := Classical.not_not.mp hnl
            exact hcon k2 (agree_trans (agree_mono a2 (by omega))
              (agree_trans (agree_symm hag) (agree_symm (agree_mono af (by omega))))) (by omega)
          · rw [heq2] at a2
            exact hvia _ (min g2 f1) (agree_mono a2 (by omega)) (agree_mono af (by omega)) (by omega)
          · have hnl := hLC _ kf pcf (hCo _ _ _ hcf).1 (hCo _ _ _ hcf).2 _ hgt2 (by omega) hl2
            unfold lacks at hnl
            obtain ⟨hkfl, hag⟩ := Classical.not_not.mp hnl
            have hl2' : σ.len0 (termAt L g2) < g2 := by
              obtain ⟨ℓ2, hℓ2⟩ := Option.ne_none_iff_exists'.mp hl2
              exact llog_own_gt_len0 hL hℓ2 (by omega) (agree_termAt a2 (Nat.le_refl _)).symm
            exact lacksF ⟨by omega, agree_trans (agree_mono a2 (by omega)) hag⟩
      · exfalso
        rw [heq] at ag
        exact hvia _ (min g1 f1) (agree_mono ag (by omega)) (agree_mono af (by omega)) (by omega)
      · exfalso
        have t4 := hLterm g1 (by omega) hg1L
        rcases Nat.lt_or_eq_of_le t4 with hlt | heq
        · have hcg' := (hCo _ _ _ hcg).1
          have hnl := hLC _ kg pcg hcg' (hCo _ _ _ hcg).2 T hlt hT'' hl
          unfold lacks at hnl
          obtain ⟨_, hag⟩ := Classical.not_not.mp hnl
          have hagL : agree L (σ.llog T) kg :=
            agree_trans (agree_mono ag (by omega)) (agree_symm hag)
          have hkd := hd_max kg hagL
          have hk1 := hcg'.2.1
          have t1 : termAt (σ.llog T) kg = termAt L g1 := by
            rw [agree_termAt hag (Nat.le_refl _)]; exact hcg'.2.2.2.1
          have t2 := LMok_term_mono hG hL hLtM hk1 (by omega : kg ≤ f1) hf1len
          omega
        · rw [heq] at ag
          exact hcon g1 ag hg1d

/-- A voter of the election of `T'` (a quorum member of the leader's election log `E`) that
acknowledged a committed prefix of an earlier term gives it to `E`, when no leader in between
lacks it. -/
theorem voter_has {σ : PState} (hG : IGen σ) (hL : ILeaders σ) (hLo : ILogs σ) (hV : IVotes σ)
    (hVA : IVoteAck σ) {T' : Nat} {ℓ : SID} (hℓ : σ.leader T' = some ℓ)
    {T0 k0 : Nat} (hc : committed σ T0 k0 p0) (hT : T0 < T') {j : SID} {m : Nat}
    (ha : σ.acked j T0 m) (hkm : k0 ≤ m) {L : RLog} (hv : σ.votes j T' = some (ℓ, L, true))
    (IH : ∀ t, T0 < t → t < T' → σ.leader t ≠ none → ¬ lacks σ t k0 T0) :
    agree ((σ.llog T').take (σ.len0 T')) (σ.llog T0) k0 := by
  obtain ⟨_, _, _, hlen0, _, hel, _, hcand, _⟩ := hL.1 T' ℓ hℓ
  have hLag : agree L (σ.llog T0) k0 := by
    rcases hVA j T' ℓ L true T0 m k0 hv ha hkm hT with h | ⟨T2, h1, h2, h3, h4⟩
    · exact h
    · rcases h2 with h2 | ⟨_, h2⟩
      · exact absurd h4 (IH T2 h1 h2 h3)
      · cases h2
  obtain ⟨li, lt, hc', hu⟩ := (hV.1 j T' ℓ L true hv).2.2.2.1
  rw [hcand] at hc'
  cases hc'
  have hElen : ((σ.llog T').take (σ.len0 T')).length = σ.len0 T' := by simp; omega
  have hE : LMok σ ((σ.llog T').take (σ.len0 T')) := LMok_take (hLo.2.1 T') _
  have hEb : ∀ x, 1 ≤ x → x ≤ ((σ.llog T').take (σ.len0 T')).length →
      termAt ((σ.llog T').take (σ.len0 T')) x < T' := by
    intro x h1 h2
    rw [hElen] at h2
    rw [termAt_take _ _ _ h2]
    exact hel x h1 h2
  have hu' : upToDate ((σ.llog T').take (σ.len0 T')).length
      (lastTerm ((σ.llog T').take (σ.len0 T'))) L := by rw [hElen]; exact hu
  exact utd hG hL hc.1 hc.2.1 hc.2.2.2.1 hE hEb (hLo.2.2.1 j T' ℓ L true hv) hLag hu' IH

/-- **Leader completeness from the other conjuncts** (stage 4: with the R-commits and the recorded
commits; moved here from `LC.lean`, as it needs `CL0`). By strong induction on the later term `T'`:
the election log `E` of `T'` has last term `≤ T` (else the leader of that term, below `T'`, holds
the prefix, and so does `E`); `CL0` on `E` gives a committed prefix `E` lacks whose quorum meets
`E`'s election quorum; a common voter gives it to `E` (`voter_has`). -/
theorem ILC_of {σ : PState} (hG : IGen σ) (hL : ILeaders σ) (hLo : ILogs σ) (hV : IVotes σ)
    (hVA : IVoteAck σ) (hR : ICfgR σ)
    (hCo : ∀ T k p, σ.commits T k p → committed σ T k p ∧ cfgAdm σ T k p) : ILC σ := by
  have main : ∀ T', ∀ T k p, committed σ T k p → cfgAdm σ T k p → T < T' →
      σ.leader T' ≠ none → ¬ lacks σ T' k T := by
    intro T'
    induction T' using Nat.strongRecOn with
    | _ T' IH =>
    intro T k p hc ha hTT' hld hlacks
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hld
    have hLT' := hL.1 T' ℓ hℓ
    obtain ⟨_, _, hlen1, hlen0, _, hel, _, hcand, ⟨QE, hQE, hQEv⟩, _⟩ := hLT'
    have hElen : ((σ.llog T').take (σ.len0 T')).length = σ.len0 T' := by simp; omega
    have hE : LMok σ ((σ.llog T').take (σ.len0 T')) := LMok_take (hLo.2.1 T') _
    have hlackE : ∀ T0 k0, ¬ (k0 ≤ ((σ.llog T').take (σ.len0 T')).length ∧
        agree ((σ.llog T').take (σ.len0 T')) (σ.llog T0) k0) → lacks σ T' k0 T0 := by
      intro T0 k0 h ⟨h1, h2⟩
      exact h ⟨by omega, agree_take_left _ h2 h1⟩
    have hlE : ¬ (k ≤ ((σ.llog T').take (σ.len0 T')).length ∧
        agree ((σ.llog T').take (σ.len0 T')) (σ.llog T) k) := by
      intro ⟨h1, h2⟩
      exact hlacks ⟨by omega, agree_of_take h2⟩
    -- a meeting voter contradicts a lack
    have hvoter : ∀ T0 k0 p0, committed σ T0 k0 p0 → cfgAdm σ T0 k0 p0 → T0 < T' →
        cfgMeet (cfgOf σ ((σ.llog T').take (σ.len0 T'))) (cfgAt σ (σ.llog T0) p0) →
        agree ((σ.llog T').take (σ.len0 T')) (σ.llog T0) k0 := by
      intro T0 k0 p0 hc0 ha0 hT0 hm
      obtain ⟨_, _, _, _, e0, he0, _, Q0, hQ0, hQ0a⟩ := id hc0
      have hcf : cfgAt σ (σ.llog T0) p0 = σ.cv e0.data := by simp [cfgAt, cfgAtC, he0]
      rw [hcf] at hm
      obtain ⟨j, hjE, hj0⟩ := hm QE Q0 hQE hQ0
      obtain ⟨m, hkm, hack⟩ := hQ0a j hj0
      obtain ⟨L, hv⟩ := hQEv j hjE
      exact voter_has hG hL hLo hV hVA hℓ hc0 hT0 hack hkm hv
        (fun t h1 h2 h3 => IH t h2 T0 k0 p0 hc0 ha0 h1 h3)
    -- the election log's last term is at most `T`
    have hET : lastTerm ((σ.llog T').take (σ.len0 T')) ≤ T := by
      apply Classical.byContradiction; intro hgt
      have hgt : T < lastTerm ((σ.llog T').take (σ.len0 T')) := by omega
      have hn : 1 ≤ ((σ.llog T').take (σ.len0 T')).length := by omega
      have hEa := hE _ hn (Nat.le_refl _)
      have hlt' : termAt ((σ.llog T').take (σ.len0 T')) ((σ.llog T').take (σ.len0 T')).length =
          lastTerm ((σ.llog T').take (σ.len0 T')) := rfl
      rw [hlt'] at hEa
      have hT2 := leader_ge_two hL hc.1
      have hld2 : σ.leader (lastTerm ((σ.llog T').take (σ.len0 T'))) ≠ none :=
        llog_leader hL (by omega) (by have := hEa.2.1; omega)
      have hlt : lastTerm ((σ.llog T').take (σ.len0 T')) < T' := by
        unfold lastTerm; rw [hElen, termAt_take _ _ _ (Nat.le_refl _)]
        exact hel _ hlen1 (Nat.le_refl _)
      have hnl := IH _ hlt T k p hc ha hgt hld2
      unfold lacks at hnl
      obtain ⟨hk0, hag2⟩ := Classical.not_not.mp hnl
      obtain ⟨ℓ2, hℓ2⟩ := Option.ne_none_iff_exists'.mp hld2
      have := llog_own_gt_len0 hL hℓ2 hn (agree_termAt hEa (Nat.le_refl _)).symm
      exact hlE ⟨by omega, agree_trans (agree_mono hEa (by omega)) hag2⟩
    obtain ⟨q, hkq, hq, hpq⟩ := ha
    have hna : ¬ (q ≤ ((σ.llog T').take (σ.len0 T')).length ∧
        agree ((σ.llog T').take (σ.len0 T')) (σ.llog T) q) := by
      intro ⟨h1, h2⟩; exact hlE ⟨by omega, agree_mono h2 hkq⟩
    rcases CL0' σ T' hG hL hLo hR hCo
        (fun T0 k0 p0 hc0 ha0 T2 h1 h2 h3 => IH T2 h2 T0 k0 p0 hc0 ha0 h1 h3)
        _ hE T q p hET hTT' hc.1 hq hpq hna with hm | ⟨T0, k0, p0, hc0, hT0, hl0, hm⟩
    · exact hlE ⟨(hvoter T k p hc ⟨q, hkq, hq, hpq⟩ hTT' hm).1,
        hvoter T k p hc ⟨q, hkq, hq, hpq⟩ hTT' hm⟩
    · have h0 := hCo _ _ _ hc0
      have := hvoter T0 k0 p0 h0.1 h0.2 (by omega) hm
      exact hl0 ⟨this.1, this⟩
  intro T k p hc ha T' hTT' hld
  exact main T' T k p hc ha hTT' hld

/-! ### Election safety -/

/-- A nonempty history log has a last term `≥ 1`; with last term `1` it is `[g]`'s length. -/
theorem LMok_last_pos {σ : PState} (hG : IGen σ) (hL : ILeaders σ) {X : RLog} (hX : LMok σ X)
    (h : 1 ≤ X.length) : 1 ≤ lastTerm X ∧ (lastTerm X = 1 → X.length = 1) := by
  have a := hX X.length h (Nat.le_refl _)
  have e : termAt X X.length = lastTerm X := rfl
  rw [e] at a
  constructor
  · apply Classical.byContradiction; intro h0
    have : lastTerm X = 0 := by omega
    rw [this, hG.2.2.2.2.2.2.2.2] at a
    have h3 := a.2.1; simp only [List.length_nil] at h3; omega
  · intro h1
    rw [h1, hG.2.2.2.2.1] at a
    have h3 := a.2.1; simp only [List.length_cons, List.length_nil] at h3; omega

/-- **Two election logs' configurations meet** (the pure core of `elect_safety`): two history logs
with last terms below `T`, the first of the smaller last term, each lacking no recorded commit of a
term `< T` whose configuration meets its own. -/
theorem two_logs_meet {σ : PState} (hG : IGen σ) (hL : ILeaders σ) (hLo : ILogs σ) (hR : ICfgR σ)
    (hCo : ∀ T k p, σ.commits T k p → committed σ T k p ∧ cfgAdm σ T k p) (hLC : ILC σ)
    {T : Nat} {S O : RLog} (hS : LMok σ S) (hO : LMok σ O) (hOT : lastTerm O < T)
    (hSO : lastTerm S ≤ lastTerm O)
    (VS : ∀ T' k' p', σ.commits T' k' p' → T' < T → ¬ (k' ≤ S.length ∧ agree S (σ.llog T') k') →
      cfgMeet (cfgOf σ S) (cfgAt σ (σ.llog T') p') → False)
    (VO : ∀ T' k' p', σ.commits T' k' p' → T' < T → ¬ (k' ≤ O.length ∧ agree O (σ.llog T') k') →
      cfgMeet (cfgOf σ O) (cfgAt σ (σ.llog T') p') → False) :
    cfgMeet (cfgOf σ S) (cfgOf σ O) := by
  by_cases hS0 : S = []
  · subst hS0; rw [cfgOf_nil]; exact cfgMeet_nil_left _
  by_cases hO0 : O = []
  · subst hO0; rw [cfgOf_nil]; exact cfgMeet_nil_right _
  have hSn : 1 ≤ S.length := by cases S with | nil => exact absurd rfl hS0 | cons _ _ => simp
  have hOn : 1 ≤ O.length := by cases O with | nil => exact absurd rfl hO0 | cons _ _ => simp
  have aO := hO O.length hOn (Nat.le_refl _)
  have eO : termAt O O.length = lastTerm O := rfl
  rw [eO] at aO
  have hOeq : O = (σ.llog (lastTerm O)).take O.length := by
    have := aO.2.2; rw [List.take_length] at this; exact this
  by_cases hext : O.length ≤ S.length ∧ agree S (σ.llog (lastTerm O)) O.length
  · ---- `S` extends `O`
    have hSO' : agree S O O.length := agree_trans hext.2 (agree_symm aO)
    have hOt : S.take O.length = O := by
      have := hSO'.2.2; rwa [List.take_length] at this
    have hcO : cfgOf σ O = cfgAt σ S (lastCfgIdx (S.take O.length)) := by
      rw [← cfgOf_take σ S, hOt]
    rw [hcO]
    by_cases hnc : ∀ k, O.length < k → k ≤ S.length → isCfgAt S k = false
    · show cfgMeet (cfgAt σ S (lastCfgIdx S)) _
      rw [lastCfgIdx_eq_lc hext.1 hnc]
      exact cfgMeet_refl _
    · have hex : ∃ k, O.length < k ∧ k ≤ S.length ∧ isCfgAt S k = true := by
        apply Classical.byContradiction; intro hn
        apply hnc; intro k h1 h2
        cases hc : isCfgAt S k
        · rfl
        · exact absurd ⟨k, h1, h2, hc⟩ hn
      obtain ⟨f1, hf1d, hf1L, hf1c, hf1m⟩ := first_cfg hex
      have hpf1 : lastCfgIdx (S.take (f1 - 1)) = lastCfgIdx (S.take O.length) :=
        (lc_noCfg (by omega) (by omega) (fun k h1 h2 => hf1m k h1 (by omega))).symm
      obtain ⟨_, _, _, _, _, _, _, hm1, _⟩ := cfgR_hist hG hL hLo hR hS hf1c (by omega)
      rw [hpf1] at hm1
      by_cases hl1 : lastCfgIdx S = f1
      · show cfgMeet (cfgAt σ S (lastCfgIdx S)) _
        rw [hl1]; exact cfgMeet_symm hm1
      · exfalso
        obtain ⟨x1, x2, x3⟩ := lastCfgIdx_isLast S
        have hge : f1 ≤ lastCfgIdx S := by
          apply Classical.byContradiction; intro h
          rw [x3 f1 (by omega) hf1L] at hf1c; cases hf1c
        have hlc : isCfgAt S (lastCfgIdx S) = true := by
          rcases x2 with h | h
          · omega
          · exact h
        obtain ⟨f2, hf2d, hf2L, hf2c, hf2m⟩ :=
          first_cfg (X := S) (a := f1) (b := S.length) ⟨lastCfgIdx S, by omega, x1, hlc⟩
        have hpf2 : lastCfgIdx (S.take (f2 - 1)) = f1 := by
          rw [← lc_self (L := S) (by omega) hf1c]
          exact (lc_noCfg (by omega) (by omega) (fun k h1 h2 => hf2m k h1 (by omega))).symm
        obtain ⟨_, _, _, hl2, a2, _, _, _, k2, pc2, q2, hc2, _, hk2a, hk2b, hk2c, hpc2⟩ :=
          cfgR_hist hG hL hLo hR hS hf2c (by omega)
        have hch := pc_char a2 hk2a hk2b hk2c hpc2
        rw [hpf2, hpf1] at hch
        rw [hpf2] at hk2a
        have ht2 : termAt S f2 < T := by
          have := LMok_le_last hG hL hS (by omega) hf2L; omega
        apply VO _ k2 pc2 hc2 ht2 (fun ⟨h1, _⟩ => by omega)
        rw [hcO, cfgAt_agree σ (agree_symm a2) (by rcases hch with h | ⟨_, h⟩ <;> omega)]
        rcases hch with h | ⟨_, h⟩
        · rw [h]; exact hm1
        · rw [h]; exact cfgMeet_refl _
  · ---- `CL0` on `S` against `O`'s leader log
    have hOl1 : 2 ≤ lastTerm O := by
      have ⟨p1, p2⟩ := LMok_last_pos hG hL hO hOn
      apply Classical.byContradiction; intro h
      have h1 : lastTerm O = 1 := by omega
      have hO1 := p2 h1
      have ⟨s1, s2⟩ := LMok_last_pos hG hL hS hSn
      have hS1 := s2 (by omega)
      apply hext
      refine ⟨by omega, ?_⟩
      rw [hO1, h1]
      have aS := hS 1 (Nat.le_refl _) (by omega)
      have : termAt S 1 = 1 := by
        have := LMok_term_mono hG hL hS (Nat.le_refl _) (Nat.le_refl _) (by omega : 1 ≤ S.length)
        have e : termAt S S.length = lastTerm S := rfl
        rw [hS1] at e; omega
      rw [this] at aS; exact aS
    have hlO : σ.leader (lastTerm O) ≠ none := llog_leader hL (by omega) (by have := aO.2.1; omega)
    have hadm : cfgAdmAt σ (lastTerm O) O.length (lastCfgIdx O) := by
      left; conv => lhs; rw [hOeq]
    rcases CL0' σ T hG hL hLo hR hCo (fun T0 k0 p0 hc0 ha0 T2 h1 h2 h3 => hLC T0 k0 p0 hc0 ha0 T2 h1 h3)
        S hS (lastTerm O) O.length (lastCfgIdx O) hSO hOT hlO aO.2.1 hadm hext with
      hm | ⟨T0, k0, p0, hc0, hT0, hl0, hm⟩
    · have : cfgAt σ (σ.llog (lastTerm O)) (lastCfgIdx O) = cfgOf σ O :=
        (cfgAt_agree σ aO (lastCfgIdx_le O)).symm
      rw [this] at hm; exact hm
    · exact absurd hm (fun hm => VS T0 k0 p0 hc0 (by omega) hl0 hm)

/-- `elect_safety` with the candidate's recorded last term below the election's term (see
`notes/s4-proto.md`, HUB-REQUEST P4-1: without it the statement fails in the model). -/
theorem elect_safety_lt (σ : PState) (hP : PInv σ) (T : Nat) (ℓ c : SID) (L : RLog) (Q : List SID)
    (hl : σ.leader T = some ℓ) (hLM : LMok σ L) (hLT : lastTerm L < T)
    (hc : σ.cand c T = some (L.length, lastTerm L)) (hQ : isQuorumOf (cfgOf σ L) Q)
    (hv : ∀ j ∈ Q, ∃ L' b, σ.votes j T = some (c, L', b)) : ℓ = c := by
  obtain ⟨hG, hL, hLo, _, hV, _, hVA, hLC, hCm, _, _, _, _, hR⟩ := hP
  have hCo : ∀ T k p, σ.commits T k p → committed σ T k p ∧ cfgAdm σ T k p :=
    fun T k p h => ⟨(hCm.1 T k p h).1, (hCm.1 T k p h).2.1⟩
  obtain ⟨_, _, hlen1, hlen0, _, hel, _, hcand, ⟨QE, hQE, hQEv⟩, _⟩ := hL.1 T ℓ hl
  have hElen : ((σ.llog T).take (σ.len0 T)).length = σ.len0 T := by simp; omega
  have hE : LMok σ ((σ.llog T).take (σ.len0 T)) := LMok_take (hLo.2.1 T) _
  have hET : lastTerm ((σ.llog T).take (σ.len0 T)) < T := by
    unfold lastTerm; rw [hElen, termAt_take _ _ _ (Nat.le_refl _)]
    exact hel _ hlen1 (Nat.le_refl _)
  have VE : ∀ T' k' p', σ.commits T' k' p' → T' < T →
      ¬ (k' ≤ ((σ.llog T).take (σ.len0 T)).length ∧ agree ((σ.llog T).take (σ.len0 T)) (σ.llog T') k') →
      cfgMeet (cfgOf σ ((σ.llog T).take (σ.len0 T))) (cfgAt σ (σ.llog T') p') → False := by
    intro T' k' p' hc' hT' hlk _
    have hnl := hLC T' k' p' (hCo _ _ _ hc').1 (hCo _ _ _ hc').2 T hT' (by rw [hl]; simp)
    unfold lacks at hnl
    obtain ⟨h1, h2⟩ := Classical.not_not.mp hnl
    exact hlk ⟨by omega, agree_take_left _ h2 h1⟩
  have VL : ∀ T' k' p', σ.commits T' k' p' → T' < T → ¬ (k' ≤ L.length ∧ agree L (σ.llog T') k') →
      cfgMeet (cfgOf σ L) (cfgAt σ (σ.llog T') p') → False := by
    intro T' k' p' hc' hT' hlk hm
    have hcm := (hCo _ _ _ hc').1
    have hca := (hCo _ _ _ hc').2
    obtain ⟨hl', hk1, _, hkt, e0, he0, _, Q0, hQ0, hQ0a⟩ := id hcm
    have hcf : cfgAt σ (σ.llog T') p' = σ.cv e0.data := by simp [cfgAt, cfgAtC, he0]
    rw [hcf] at hm
    obtain ⟨j, hjL, hj0⟩ := hm Q Q0 hQ hQ0
    obtain ⟨m, hkm, hack⟩ := hQ0a j hj0
    obtain ⟨L', b, hvj⟩ := hv j hjL
    have hL'ag : agree L' (σ.llog T') k' := by
      rcases hVA j T c L' b T' m k' hvj hack hkm hT' with h | ⟨T2, h1, h2, h3, h4⟩
      · exact h
      · exact absurd h4 (hLC T' k' p' hcm hca T2 h1 h3)
    obtain ⟨li, lt, hc'', hu⟩ := (hV.1 j T c L' b hvj).2.2.2.1
    rw [hc] at hc''
    cases hc''
    have hEb : ∀ x, 1 ≤ x → x ≤ L.length → termAt L x < T := fun x h1 h2 =>
      Nat.lt_of_le_of_lt (LMok_le_last hG hL hLM h1 h2) hLT
    have hag := utd hG hL hl' hk1 hkt hLM hEb (hLo.2.2.1 j T c L' b hvj) hL'ag hu
      (fun t h1 h2 h3 => hLC T' k' p' hcm hca t h1 h3)
    exact hlk ⟨hag.1, hag⟩
  have hmeet : cfgMeet (cfgOf σ L) (cfgOf σ ((σ.llog T).take (σ.len0 T))) := by
    by_cases hle : lastTerm L ≤ lastTerm ((σ.llog T).take (σ.len0 T))
    · exact two_logs_meet hG hL hLo hR hCo hLC hLM hE hET hle VL VE
    · exact cfgMeet_symm (two_logs_meet hG hL hLo hR hCo hLC hE hLM hLT (by omega) VE VL)
  obtain ⟨j, hjL, hjE⟩ := hmeet Q QE hQ hQE
  obtain ⟨L1, hv1⟩ := hQEv j hjE
  obtain ⟨L2, b, hv2⟩ := hv j hjL
  rw [hv1] at hv2
  cases hv2
  rfl

end proto
end github_com.hashicorp.raft
end Perennial
