/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/LeaderAppend.lean (241f27e).
-/
/-
`proto` — `leaderAppend` preserves `PInv` (the leader's log and its leader log grow together).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.SrvFrame

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

theorem ent_mem {L : RLog} {k : Nat} {e : Entry} (h : ent L k = some e) : e ∈ L := by
  unfold ent at h
  split at h
  · cases h
  · exact List.mem_of_getElem? h

/-- An entry past `L` in `L ++ es` is from `es`. -/
theorem ent_append_mem {L es : RLog} {k : Nat} {e : Entry} (h : ent (L ++ es) k = some e)
    (hk : L.length < k) : e ∈ es := by
  rw [ent_append_right _ _ _ hk] at h
  exact ent_mem h

theorem LMok_append_own {σ σ' : PState} {L es : RLog} {T : Nat}
    (hpre : ∀ t, σ.llog t <+: σ'.llog t) (hM : LMok σ L) (hT : σ'.llog T = L ++ es)
    (hes : ∀ e ∈ es, e.term = T) : LMok σ' (L ++ es) := by
  intro k h1 h2
  by_cases hk : k ≤ L.length
  · rw [termAt_append_left _ _ _ hk]
    exact agree_append_left es (agree_prefix_right (hM k h1 hk) (hpre _))
  · obtain ⟨e, he⟩ := ent_isSome _ k h1 h2
    rw [termAt_of_ent he, hes e (ent_append_mem he (by omega)), hT]
    exact agree_refl _ _ h2

/-- (stage 4) What `leaderAppend` and `leaderAppendCfg` share: the leader of its current term
appends entries of its term. -/
def laBase (σ : PState) (i : SID) (es : RLog) : Prop :=
  i ∈ σ.srvs ∧ σ.leader (σ.term i) = some i ∧ ∀ e ∈ es, e.term = σ.term i

/-- The precondition, with the entry kinds weakened to "not a configuration". -/
theorem la_pre_old {σ : PState} {i : SID} {es : RLog} (hp : leaderAppendPre σ i es) :
    i ∈ σ.srvs ∧ σ.leader (σ.term i) = some i ∧
      ∀ e ∈ es, e.term = σ.term i ∧ e.kind ≠ kConfig := by
  refine ⟨hp.1, hp.2.1, fun e he => ⟨(hp.2.2 e he).1, ?_⟩⟩
  rcases (hp.2.2 e he).2 with h | h | h <;> rw [h] <;> decide

theorem la_base {σ : PState} {i : SID} {es : RLog} (hp : leaderAppendPre σ i es) : laBase σ i es :=
  ⟨hp.1, hp.2.1, fun e he => (hp.2.2 e he).1⟩

section
variable {σ : PState} {i : SID} {es : RLog} (h : PInv σ) (hp : laBase σ i es)
include h hp

theorem la_T2 : 2 ≤ σ.term i := by
  obtain ⟨_, hL, _⟩ := h
  exact (hL.1 _ i hp.2.1).2.1

theorem la_log : σ.log i = σ.llog (σ.term i) := by
  obtain ⟨_, _, _, hC, _⟩ := h
  exact hC i hp.1 hp.2.1

theorem la_prefix : ∀ t, σ.llog t <+: (leaderAppend σ i es).llog t := by
  intro t
  show σ.llog t <+: updT σ.llog (σ.term i) (σ.log i ++ es) t
  by_cases ht : t = σ.term i
  · subst ht; rw [updT_same, la_log h hp]; exact List.prefix_append _ _
  · rw [updT_ne _ _ _ _ ht]; exact List.prefix_refl _

theorem la_HG : HG σ (leaderAppend σ i es) :=
  ⟨rfl, fun _ _ x => x, la_prefix h hp, fun _ _ => rfl, rfl⟩

theorem lab_llog (t : Nat) :
    (leaderAppend σ i es).llog t = if t = σ.term i then σ.llog t ++ es else σ.llog t := by
  show updT σ.llog (σ.term i) (σ.log i ++ es) t = _
  rw [updT_apply]
  split
  · subst_vars; rw [la_log h hp]
  · rfl

theorem la_log' (j : SID) :
    (leaderAppend σ i es).log j = if j = i then σ.log i ++ es else σ.log j :=
  setSrv_log σ i _ j

theorem la_term' (j : SID) : (leaderAppend σ i es).term j = σ.term j := by
  show (setSrv σ i _).term j = _
  rw [setSrv_term]; split <;> (subst_vars; rfl)

theorem la_ILeaders
    (hadm : cfgAdmAt (leaderAppend σ i es) (σ.term i) (σ.llog (σ.term i) ++ es).length
      (σ.ccfg (σ.term i))) : ILeaders (leaderAppend σ i es) := by
  have hT2 := la_T2 h hp
  have hll := lab_llog h hp
  obtain ⟨hG, hL, hLo, hC, hV, _⟩ := h
  obtain ⟨hi, hld, hes⟩ := hp
  refine ⟨fun T ℓ hl => ?_, fun T h1 hl => ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, ⟨Q, hQ, hQv⟩, a10⟩ := hL.1 T ℓ hl
    have hl0 : (leaderAppend σ i es).len0 T = σ.len0 T := rfl
    have hcc : (leaderAppend σ i es).ccfg T = σ.ccfg T := rfl
    rw [hl0, hll, hcc]
    split
    · subst_vars
      refine ⟨a1, a2, a3, by simp; omega, ?_, ?_, ?_, ?_, ⟨Q, ?_, hQv⟩, hadm⟩
      · rw [ent_append_left _ _ _ (by omega)]; exact a5
      · intro k h1 h2; rw [termAt_append_left _ _ _ (by omega)]; exact a6 k h1 h2
      · intro k e hk he
        by_cases hk' : k ≤ (σ.llog (σ.term i)).length
        · rw [ent_append_left _ _ _ hk'] at he; exact a7 k e hk he
        · exact hes e (ent_append_mem he (by omega))
      · rw [List.take_append_of_le_length a4]; exact a8
      · rw [List.take_append_of_le_length a4]; exact hQ
    · rename_i hT
      refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, ⟨Q, hQ, hQv⟩, ?_⟩
      exact (cfgAdmAt_congr (σ' := leaderAppend σ i es) (σ := σ) (by rw [hll, if_neg' hT]) rfl).mpr a10
  · have hl' : σ.leader T = none := hl
    have : T ≠ σ.term i := by intro e; subst e; rw [hld] at hl'; cases hl'
    rw [hll, if_neg' this]
    exact hL.2 T h1 hl

theorem la_ILogs (hcfg : ∀ e ∈ es, e.kind = kConfig → cfgValid σ.srvs (σ.cv e.data)) :
    ILogs (leaderAppend σ i es) := by
  have hpre := la_prefix h hp
  have hll := lab_llog h hp
  have hlg := la_log h hp
  have hlog' := la_log' h hp
  obtain ⟨hG, hL, hLo, hC, hV, _⟩ := h
  obtain ⟨hi, hld, hes⟩ := hp
  obtain ⟨l1, l2, l3, l4, l5⟩ := hLo
  have hown : LMok (leaderAppend σ i es) (σ.log i ++ es) :=
    LMok_append_own hpre (l1 i hi).1 (by rw [hll, if_pos' rfl, hlg]) hes
  have hg1 : ent (σ.log i) 1 = some σ.g := by rw [hlg]; exact (hL.1 _ i hld).2.2.2.2.1
  refine ⟨fun j hj => ?_, fun T => ?_, fun j T c L b hv => LMok_mono hpre (l3 j T c L b hv),
    LMok_mono hpre l4, fun T k e he hk => ?_⟩
  · rw [hlog']; split
    · refine ⟨hown, Or.inr ?_⟩
      rw [ent_append_left _ _ _ (ent_le_length hg1).2]; exact hg1
    · exact ⟨LMok_mono hpre (l1 j hj).1, (l1 j hj).2⟩
  · rw [hll]; split
    · subst_vars; rw [← hlg]; exact hown
    · exact LMok_mono hpre (l2 T)
  · show cfgValid σ.srvs (σ.cv e.data)
    rw [hll] at he
    split at he
    · by_cases hk' : k ≤ (σ.llog T).length
      · rw [ent_append_left _ _ _ hk'] at he; exact l5 T k e he hk
      · exact hcfg e (ent_append_mem he (by omega)) hk
    · exact l5 T k e he hk

theorem la_ICfgR
    (hnew : ∀ p e, (σ.log i).length < p → ent (σ.log i ++ es) p = some e → e.kind = kConfig →
      adjV (cfgOf σ ((σ.log i ++ es).take (p - 1))) (σ.cv e.data) ∧
      ∃ k pc q, σ.commits (σ.term i) k pc ∧ σ.len0 (σ.term i) < k ∧
        lastCfgIdx ((σ.log i ++ es).take (p - 1)) ≤ k ∧ k ≤ q ∧ q < p ∧
        cfgAdmAt (leaderAppend σ i es) (σ.term i) q pc) :
    ICfgR (leaderAppend σ i es) := by
  have hg := la_HG h hp
  have hll := lab_llog h hp
  have hlg := la_log h hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := h
  intro T p e h1 h2 h3 h4
  by_cases hp' : p ≤ (σ.llog T).length
  · have e3 : ent (σ.llog T) p = some e := by
      rw [← agree_ent (agree_of_prefix (hg.llog T) hp') (Nat.le_refl _)] at h3; exact h3
    obtain ⟨hadj, k, pc, q, hc, a, b, c, d, f⟩ := hR T p e h1 h2 e3 h4
    have et : ((leaderAppend σ i es).llog T).take (p - 1) = (σ.llog T).take (p - 1) :=
      (agree_of_prefix (hg.llog T) (by omega)).2.2.symm
    refine ⟨?_, k, pc, q, hc, a, by rw [et]; exact b, c, d, cfgAdmAt_grow hg h1 (by omega) f⟩
    show adjV (cfgOf σ (((leaderAppend σ i es).llog T).take (p - 1))) (σ.cv e.data)
    rw [et]; exact hadj
  · have hT : T = σ.term i := by
      apply Classical.byContradiction; intro hT
      rw [hll, if_neg' hT] at h3
      have := (ent_le_length h3).2; omega
    subst hT
    rw [hll, if_pos' rfl, ← hlg] at h3 ⊢
    rw [← hlg] at hp'
    exact hnew p e (by omega) h3 h4

theorem la_ICurrent : ICurrent (leaderAppend σ i es) := by
  have hll := lab_llog h hp
  have hlg := la_log h hp
  have hlog' := la_log' h hp
  have htm := la_term' h hp
  obtain ⟨hG, hL, hLo, hC, hV, _⟩ := h
  obtain ⟨hi, hld, hes⟩ := hp
  intro j hj hl
  rw [htm] at hl ⊢
  have hl' : σ.leader (σ.term j) = some j := hl
  rw [hlog', hll]
  by_cases hji : j = i
  · subst hji; rw [if_pos' rfl, if_pos' rfl, hlg]
  · rw [if_neg' hji]
    have : σ.term j ≠ σ.term i := by intro e; rw [e, hld] at hl'; cases hl'; exact hji rfl
    rw [if_neg' this]
    exact hC j hj hl'

theorem la_inv_gen
    (hadm : cfgAdmAt (leaderAppend σ i es) (σ.term i) (σ.llog (σ.term i) ++ es).length
      (σ.ccfg (σ.term i)))
    (hcfg : ∀ e ∈ es, e.kind = kConfig → cfgValid σ.srvs (σ.cv e.data))
    (hnew : ∀ p e, (σ.log i).length < p → ent (σ.log i ++ es) p = some e → e.kind = kConfig →
      adjV (cfgOf σ ((σ.log i ++ es).take (p - 1))) (σ.cv e.data) ∧
      ∃ k pc q, σ.commits (σ.term i) k pc ∧ σ.len0 (σ.term i) < k ∧
        lastCfgIdx ((σ.log i ++ es).take (p - 1)) ≤ k ∧ k ≤ q ∧ q < p ∧
        cfgAdmAt (leaderAppend σ i es) (σ.term i) q pc) :
    PInv (leaderAppend σ i es) ∧ Grows σ (leaderAppend σ i es) := by
  have hg := la_HG h hp
  have hL' := la_ILeaders h hp hadm
  have hLo' := la_ILogs h hp hcfg
  have hC' := la_ICurrent h hp
  have hR' := la_ICfgR h hp hnew
  have hll := lab_llog h hp
  have hlg := la_log h hp
  have hlog' := la_log' h hp
  have htm := la_term' h hp
  have hT2 := la_T2 h hp
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  obtain ⟨hi, hld, hes⟩ := hp
  have hG' : IGen (leaderAppend σ i es) := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hG
    refine ⟨a1, a2, a3, a4, ?_, a6, a7, a8, ?_⟩
    · rw [hll, if_neg' (by omega)]; exact a5
    · rw [hll, if_neg' (by omega)]; exact a9
  have hsrv : ∀ j, ((leaderAppend σ i es).srv j).vterm = (σ.srv j).vterm ∧
      ((leaderAppend σ i es).srv j).vcand = (σ.srv j).vcand ∧
      ((leaderAppend σ i es).srv j).dur = (σ.srv j).dur ∧
      ((leaderAppend σ i es).srv j).cidx = (σ.srv j).cidx := by
    intro j; unfold leaderAppend; simp only [upd_apply]
    split <;> (subst_vars; exact ⟨rfl, rfl, rfl, rfl⟩)
  have hV' : IVotes (leaderAppend σ i es) :=
    IVotes_srv (σ := σ) rfl rfl rfl rfl (fun j => ⟨(hsrv j).1, (hsrv j).2.1⟩)
      (fun j => by rw [htm]; exact Nat.le_refl _) hV
  have hlogs : ∀ j ∈ σ.srvs, σ.log j <+: (leaderAppend σ i es).log j := by
    intro j _; rw [hlog']; split
    · subst_vars; exact List.prefix_append _ _
    · exact List.prefix_refl _
  have hterm : ∀ j ∈ σ.srvs, σ.term j ≤ (leaderAppend σ i es).term j :=
    fun j _ => by rw [htm]; exact Nat.le_refl _
  have hA' := IAcks_grow hg hL hlogs hterm (fun _ _ _ x => x) hA
  have hVA' := IVoteAck_grow hg hL hA (fun _ _ _ x => x) (fun _ _ _ x => x) hVA
  have hB' : IBounds (leaderAppend σ i es) := by
    obtain ⟨b1, b2, b3, b4, b5⟩ := hB
    have hmx : (leaderAppend σ i es).maxI = max σ.maxI ((σ.log i).length + es.length) := rfl
    refine ⟨fun j hj => ?_, fun T => ?_, b3, b4, by rw [hmx]; omega⟩
    · rw [htm, hlog', hmx]; split
      · simp; exact ⟨(b1 j hj).1, by omega⟩
      · exact ⟨(b1 j hj).1, by have := (b1 j hj).2; omega⟩
    · rw [hll, hmx]; split
      · subst_vars; rw [← hlg]; simp; omega
      · have := b2 T; omega
  have hX' : IAux (leaderAppend σ i es) := by
    intro j hj
    rw [htm, hlog']; split
    · subst_vars
      refine ⟨fun _ => by omega, fun k h1 h2 => ?_⟩
      by_cases hk : k ≤ (σ.log j).length
      · rw [termAt_append_left _ _ _ hk]; exact (hX j hj).2 k h1 hk
      · obtain ⟨e, he⟩ := ent_isSome _ k h1 h2
        rw [termAt_of_ent he, hes e (ent_append_mem he (by omega))]
        exact Nat.le_refl _
    · exact hX j hj
  have hCo' : ICommits (leaderAppend σ i es) :=
    ICommits_grow hg (fun _ _ _ x => x) (fun _ _ _ => Iff.rfl) rfl hCo
  refine ⟨⟨hG', hL', hLo', hC', hV', hA', hVA',
    ILC_of hG' hL' hLo' hV' hVA' hR' (fun T k p hc => ⟨(hCo'.1 T k p hc).1, (hCo'.1 T k p hc).2.1⟩),
    hCo',
    IDur_grow hg hlogs hterm (fun j _ => ⟨(hsrv j).2.2.1, (hsrv j).2.2.2⟩) (fun _ _ _ x => x) hD,
    hB', hX', IPub_grow hg hterm (fun j _ => by rw [(hsrv j).2.2.1]) (fun _ _ _ x => x) rfl hP, hR'⟩, ?_⟩
  refine ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨hg.llog T, fun _ => rfl⟩, fun _ _ _ x => x,
    fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
    fun j => by rw [htm]; exact Nat.le_refl _, fun j => by rw [(hsrv j).2.2.1]; exact Nat.le_refl _,
    Nat.le_refl _, ?_, fun _ _ x => x, fun _ _ _ _ x => Or.inl x⟩
  show σ.maxI ≤ max σ.maxI _
  omega

end

/-- The leader logs after `leaderAppend` (the stage-3 form, used by gprot). -/
theorem la_llog {σ : PState} {i : SID} {es : RLog} (h : PInv σ) (hp : leaderAppendPre σ i es)
    (t : Nat) :
    (leaderAppend σ i es).llog t = if t = σ.term i then σ.llog t ++ es else σ.llog t :=
  lab_llog h (la_base hp) t

/-- **leaderAppend** (commands, no-ops, barriers) keeps the invariant. -/
theorem la_inv {σ : PState} {i : SID} {es : RLog} (h : PInv σ) (hp : leaderAppendPre σ i es) :
    PInv (leaderAppend σ i es) ∧ Grows σ (leaderAppend σ i es) := by
  have hb := la_base hp
  have hll := lab_llog h hb
  have hlg := la_log h hb
  obtain ⟨hi, hld, hes⟩ := la_pre_old hp
  have hnc : ∀ e ∈ es, e.kind ≠ kConfig := fun e he => (hes e he).2
  refine la_inv_gen h hb ?_ (fun e he hk => absurd hk (hnc e he)) ?_
  · obtain ⟨_, hL, _⟩ := h
    have a10 := (hL.1 _ i hld).2.2.2.2.2.2.2.2.2
    have a4 := (hL.1 _ i hld).2.2.2.1
    unfold cfgAdmAt at a10 ⊢
    rw [hll, if_pos' rfl, List.take_length, lastCfgIdx_append_noCfg _ _ hnc]
    rw [List.take_length] at a10
    have hle := lastCfgIdx_le (σ.llog (σ.term i))
    rw [List.take_append_of_le_length (by omega)]
    exact a10
  · intro p e hp' he hk
    exact absurd hk (hnc e (ent_append_mem he hp'))

/-- (stage 4) **leaderAppendCfg** keeps the invariant: the entry's R-commit is the precondition's
commit; the commitment's configuration is the parent of the new latest (the window). -/
theorem lac_inv {σ : PState} {i : SID} {e0 : Entry} (h : PInv σ) (hp : leaderAppendCfgPre σ i e0) :
    PInv (leaderAppendCfg σ i e0) ∧ Grows σ (leaderAppendCfg σ i e0) := by
  obtain ⟨hi, hld, het, hek, hval, hadj, hcc, k, p0, hc0, hk0, hk1⟩ := hp
  have hb : laBase σ i [e0] := ⟨hi, hld, fun e he => by simp at he; subst he; exact het⟩
  have hll := lab_llog h hb
  have hlg := la_log h hb
  have hg := la_HG h hb
  unfold leaderAppendCfg
  refine la_inv_gen h hb ?_ (fun e he _ => by simp at he; subst he; exact hval) ?_
  · right
    rw [hll, if_pos' rfl, List.take_length, ← hlg, lastCfgIdx_append_cfg _ _ hek]
    obtain ⟨_, hL, _⟩ := h
    have a4 := (hL.1 _ i hld).2.2.2.1
    rw [← hlg] at a4
    refine ⟨by show σ.len0 (σ.term i) < _; omega, ?_⟩
    show σ.ccfg (σ.term i) = _
    rw [hcc]; simp
  · intro p e hp' he hk
    have hp1 : p = (σ.log i).length + 1 := by
      have := (ent_le_length he).2; simp at this; omega
    subst hp1
    rw [ent_append_right _ _ _ hp'] at he
    simp [ent] at he; subst he
    simp only [Nat.add_sub_cancel, List.take_left']
    refine ⟨hadj, ?_⟩
    obtain ⟨_, _, _, _, _, _, _, _, hCm, _⟩ := h
    obtain ⟨hcm, ⟨q, hkq, hq, hqa⟩, _⟩ := hCm.1 _ _ _ hc0
    refine ⟨k, p0, q, hc0, hk0, hk1, hkq, by rw [hlg]; omega, cfgAdmAt_grow hg hcm.1 hq hqa⟩

/-- (stage 4) **installCfg** keeps the invariant: only the commitment's configuration of `T`
changes, to the latest of `llog T` (admissible). -/
theorem installCfg_inv' {σ : PState} {T : Nat} (h : PInv σ) (hp : installCfgPre σ T) :
    PInv (installCfg σ T) ∧ Grows σ (installCfg σ T) := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  have hL' : ILeaders (installCfg σ T) := by
    refine ⟨fun T1 ℓ hl => ?_, hL.2⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hL.1 T1 ℓ hl
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, ?_⟩
    show cfgAdmAt σ T1 (σ.llog T1).length (updT σ.ccfg T (lastCfgIdx (σ.llog T)) T1)
    by_cases hT : T1 = T
    · subst hT; rw [updT_same]; left; rw [List.take_length]
    · rw [updT_ne _ _ _ _ hT]; exact a10
  exact ⟨⟨hG, hL', hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩,
    rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ x => x,
      fun _ _ _ _ x => Or.inl x⟩

end proto
end github_com.hashicorp.raft
end Perennial
