/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/gprot/Cfg.lean (241f27e).
-/
/-
`gprot` (stage 4) — membership changes in the ghost layer: the configuration entry a leader
appends (`leaderAppendCfg_upd`), the configuration its commitment counts (`ccfgOwn`,
`installCfg_upd`), the committed parent of a configuration (`cfgPrevCommitted`), what a leader
knows of its own log (`llogPre`, for the configurations of its prefixes: the read bound,
`Snap.read_bound_upd`), and the committed prefix of a server's log (`srvOwn_CLb`, the snapshot's
configuration).

Ownership of `ccfgOwn γ c T p` (half of the element `(c, T)` of `γ.ccfg`; the invariant holds the
authority, `CcfgG`): both halves go to `c`'s main goroutine at its election of `T`
(`electTerm_upd`); as leader it keeps one and puts the other in its commitment's lock
(`newCommitment`); `commitment.setConfiguration` (called by the main goroutine) joins them to
install the latest configuration (`installCfg_upd`); `recalculate` reads its half (`commit_upd`,
`commit_or_snap`); `appendConfigurationEntry` checks the main goroutine's half
(`leaderAppendCfg_upd`: the previous change was installed).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Install

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft
namespace gprot

open proto

section cfg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable (γ : GNames)

/-! ## The commitment's configuration -/

/-- The two halves of a commitment's configuration agree. -/
theorem ccfgOwn_agree (c : SID) (T p1 p2 : Nat) :
    ccfgOwn (GF := GF) γ c T p1 ∗ ccfgOwn γ c T p2 ⊢ ⌜p1 = p2⌝ := by
  unfold ccfgOwn
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree (c, T) γ.ccfg _ _ p1 p2 $$ H1 H2

/-- The configuration the leader's commitment counts is a configuration entry of its leader log
(`ILeaders`: `ccfg T` is admissible). -/
theorem ccfgOwn_entry (E : CoPset) (hE : ↑gprotN ⊆ E) (ℓ : SID) (T p : Nat) :
    Inv (GF := GF) γ ∗ leaderIs γ T ℓ ∗ ccfgOwn γ ℓ T p ⊢ |={E}=>
      ccfgOwn γ ℓ T p ∗ ∃ e, llogIdx γ T p e ∗ ⌜e.kind = kConfig⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, #Hl, Hk⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T ℓ $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hcc, Hk, %hk⟩ := CcfgG_lookup γ σ ℓ T p $$ [Hcc Hk]
  · iframe
  obtain ⟨e, he, hek⟩ := ccfg_entry hg.1 hl
  rw [hk.2 hl] at he
  ihave ⟨Hh, #He⟩ := H_llog_get γ σ T p e he $$ Hh
  isplitl [Hh Hs Hr Hcc]
  · iframe; ipureintro; exact hg
  isplitl [Hk]; · iexact Hk
  iexists e; isplitr; · iexact He
  ipureintro; exact hek

/-- **installCfg** (`commitment.setConfiguration` after `appendConfigurationEntry`'s dispatch): the
leader of its term, with both halves of its commitment's configuration, installs its latest
configuration. -/
theorem installCfg_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (p : Nat) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ leaderIs γ s.term i ∗ ccfgOwn γ i s.term p ∗
      ccfgOwn γ i s.term p ⊢ |={E}=>
      srvOwn γ i s ∗ ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
      ccfgOwn γ i s.term (lastCfgIdx s.log) := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, #Hl, Hk1, Hk2⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hLL : (σ.srv i).log = σ.llog (σ.srv i).term := leader_log σ i hP hi' hl
  obtain ⟨hP', hGr⟩ := installCfg_inv σ (σ.srv i).term hP (by show σ.leader _ ≠ none; rw [hl]; simp)
  imod CcfgG_set γ σ (installCfg σ (σ.srv i).term) i (σ.srv i).term p p (lastCfgIdx (σ.srv i).log)
    rfl
    (fun T' hT' => ⟨rfl, by simp [installCfg, updT, hT']⟩)
    (fun c' hc' => by
      have h1 : σ.leader (σ.srv i).term = some c' := hc'
      rw [hl] at h1; cases h1
      exact ⟨rfl, by simp [installCfg, updT, hLL]⟩) $$ [Hcc Hk1 Hk2] with ⟨Hcc, Hk1, Hk2⟩
  · iframe
  imod HistG_grow γ σ (installCfg σ (σ.srv i).term) hP hGr (fun T k e h _ => ⟨T, h⟩) []
    (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) []
    (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) $$ Hh with Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (installCfg σ (σ.srv i).term) σ.srv (σ.maxT + σ.maxI) rfl
      (Nat.le_refl _) (GInv_step hg hP' hGr (installCfg_kinds σ _ hg.2.2.2.2.1))
    iframe
  isplitl [Ho]; · iexact Ho
  isplitl [Hk1]; · iexact Hk1
  iexact Hk2

/-- **leaderAppendCfg** (`appendConfigurationEntry`'s `dispatchLogs`, before the log store's
`StoreLogs`): the leader of its term appends a configuration entry `e` of its term whose voters are
valid and adjacent to its latest configuration's (`nextConfiguration`), when its commitment counts
its latest configuration (its half of `ccfgOwn`) and a commit of its term covers that
configuration's index (`configurationChangeChIfStable`). Costs one receipt. -/
theorem leaderAppendCfg_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (e : Entry)
    (k p : Nat)
    (he : e.term = s.term ∧ e.kind = kConfig ∧ cfgValid γ.srvs (γ.cv e.data) ∧
      adjV (cfgOfC γ.cv s.log) (γ.cv e.data) ∧ lastCfgIdx s.log ≤ k) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ logCouple γ i s.log ∗ leaderIs γ s.term i ∗
      ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ commitIs γ s.term k p ∗ receipt 1 ⊢ |={E}=>
      srvOwn γ i { s with log := s.log ++ [e] } ∗ logCouple γ i (s.log ++ [e]) ∗
      ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ llogIdx γ s.term (s.log.length + 1) e := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hlc, #Hl, Hk, #Hcm, Hrs⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %hcm⟩ := H_commit_lookup γ σ s.term k p $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hcm
  ihave ⟨Hcc, Hk, %hk⟩ := CcfgG_lookup γ σ i s.term (lastCfgIdx s.log) $$ [Hcc Hk]
  · iframe
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hLL : (σ.srv i).log = σ.llog (σ.srv i).term := leader_log σ i hP hi' hl
  have hlen0k : σ.len0 (σ.srv i).term < k := by
    have hc := ((PInv.commits hP).1 _ _ _ hcm).1
    apply Nat.lt_of_not_le
    intro hc'
    have := ((PInv.leaders hP).1 _ _ hl).2.2.2.2.2.1 k hc.2.1 hc'
    rw [hc.2.2.2.1] at this; omega
  have hpre : leaderAppendCfgPre σ i e := by
    refine ⟨hi', hl, he.1, he.2.1, ?_, ?_, hk.2 hl, k, p, hcm, hlen0k, he.2.2.2.2⟩
    · rw [hg.2.1, hg.2.2.2.1]; exact he.2.2.1
    · show adjV (cfgOfC σ.cv (σ.srv i).log) (σ.cv e.data)
      rw [hg.2.2.2.1]; exact he.2.2.2.1
  obtain ⟨hP', hGr⟩ := leaderAppendCfg_inv σ i e hP hpre
  have hlen : (σ.srv i).log.length ≤ σ.maxI := log_le_maxI σ i hP hi'
  have hllog : ∀ T, (leaderAppendCfg σ i e).llog T =
      if T = σ.term i then σ.llog T ++ [e] else σ.llog T := by
    intro T
    show updT σ.llog (σ.term i) (σ.log i ++ [e]) T = _
    unfold updT
    split
    · rename_i hT; subst hT; rw [show σ.log i = σ.llog (σ.term i) from hLL]
    · rfl
  have oLl : ∀ x, x ∉ [(σ.term i, (σ.log i).length + 1)] →
      llogF (leaderAppendCfg σ i e) x = llogF σ x := by
    intro ⟨T, k⟩ hx
    unfold llogF; rw [hllog]
    split
    · rename_i hT
      subst hT
      have hLL' : σ.log i = σ.llog (σ.term i) := hLL
      rw [← hLL']
      by_cases hk : k ≤ (σ.log i).length
      · exact ent_append_left _ _ _ hk
      · have hk2 : (σ.log i).length + 1 < k := by
          apply Nat.lt_of_not_le
          intro hk2
          apply hx
          simp only [List.mem_singleton, Prod.mk.injEq, true_and]; omega
        rw [ent_none_of_gt _ _ (by simp; omega), ent_none_of_gt _ _ (by omega)]
    · rfl
  have hLcA : ∀ T k e', ent ((leaderAppendCfg σ i e).llog T) k = some e' → e'.kind = kCommand →
      ∃ T', ent (σ.llog T') k = some e' := by
    intro T k e' he' hk'
    rw [hllog] at he'
    split at he'
    · by_cases hk2 : k ≤ (σ.llog T).length
      · rw [proto.ent_append_left _ _ _ hk2] at he'; exact ⟨T, he'⟩
      · have := ent_append_mem he' (by omega)
        simp only [List.mem_singleton] at this
        subst this
        rw [he.2.1] at hk'; simp [kCommand, kConfig] at hk'
    · exact ⟨T, he'⟩
  have hnew : ent ((leaderAppendCfg σ i e).llog (σ.srv i).term) ((σ.srv i).log.length + 1) = some e := by
    rw [hllog, if_pos (show (σ.srv i).term = σ.term i from rfl), ← hLL]
    have := ent_append_right (σ.srv i).log [e] 0
    simpa using this
  have hrc : (leaderAppendCfg σ i e).maxT + (leaderAppendCfg σ i e).maxI ≤
      σ.maxT + σ.maxI + 1 := by
    simp only [leaderAppendCfg, leaderAppend, PState.log, List.length_singleton]; omega
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold logCouple
  icases Hlc with ⟨Hlc, #Hv⟩
  imod ghostVar_update_halves ((σ.srv i).log ++ [e]) (γ.slog i) _ _ $$ Hlg Hlc with ⟨Hlg, Hlc⟩
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with log := (σ.srv i).log ++ [e] }
    $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with log := (σ.srv i).log ++ [e] }).2 $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with log := (σ.srv i).log ++ [e] } Hi
  imod HistG_grow γ σ (leaderAppendCfg σ i e) hP hGr hLcA [] (fun _ _ => rfl)
    [(σ.term i, (σ.log i).length + 1)] oLl
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  ihave ⟨Hh, #Hent⟩ := H_llog_get γ (leaderAppendCfg σ i e) (σ.srv i).term
    ((σ.srv i).log.length + 1) e hnew $$ Hh
  ihave Hr := (receipt_add (GF := GF) (σ.maxT + σ.maxI) 1).2 $$ [Hr Hrs]
  · iframe
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (leaderAppendCfg σ i e)
      (upd σ.srv i { σ.srv i with log := (σ.srv i).log ++ [e] }) (σ.maxT + σ.maxI + 1) rfl hrc
      (GInv_step hg hP' hGr (leaderAppendCfg_kinds σ i e hP hpre hg.2.2.2.2.1))
    iframe
    iapply CcfgG_congr γ σ (leaderAppendCfg σ i e) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  isplitl [Hlc]; · iframe; iexact Hv
  isplitl [Hk]; · iexact Hk
  iexact Hent

/-! ## Configurations in the committed log -/

/-- **The committed parent** (`proto.cfg_prev_committed`; `processConfigurationLogEntry` makes the
previous latest configuration the committed one): the index of the configuration before a
configuration entry at `p` of a server's log (`0` if none) is committed by a commit of a term
`≤ s.term` whose leader log has the server's entry there (`cmtIdx`; review T1-1: the R-commit of the
entry at `p`, of its term `≤ s.term` by `IAux`, covers the parent's index, and its leader log agrees
with the server's log there by log matching). (Interface stage 4 before the review: `0 <` the
parent's index, its entry `e'`, and the conclusion `CIdx γ (parent) e'`; `cmtIdx_CIdx` gives it.) -/
theorem cfgPrevCommitted (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (p : Nat)
    (e : Entry) (he : ent s.log p = some e) (hk : e.kind = kConfig) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢ |={E}=>
      srvOwn γ i s ∗ cmtIdx γ s.term s.log (lastCfgIdx (s.log.take (p - 1))) := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  unfold cmtIdx
  by_cases h0 : lastCfgIdx ((σ.srv i).log.take (p - 1)) = 0
  · isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    isplitl [Ho]; · iexact Ho
    ileft; ipureintro; exact h0
  have hp1 := ent_pos he
  have hpl := ent_le_length he
  have hppl : lastCfgIdx ((σ.srv i).log.take (p - 1)) ≤ p - 1 :=
    Nat.le_trans (lastCfgIdx_spec _).1 (by simp only [List.length_take]; exact Nat.min_le_left _ _)
  have hag : agree (σ.srv i).log (σ.llog e.term) p := by
    have := ((PInv.logs hP).1 i hi').1 p hp1 hpl
    rw [show termAt (σ.log i) p = e.term from termAt_of_ent he] at this
    exact this
  have he' : ent (σ.llog e.term) p = some e := by rw [← agree_ent hag (Nat.le_refl _)]; exact he
  have hlne : σ.leader e.term ≠ none := by
    intro hn
    by_cases hT : e.term = 1
    · have h1 : (σ.llog e.term).length = 1 := by rw [hT, (PInv.gen hP).2.2.2.2.1]; rfl
      have := ent_le_length he'
      omega
    · rw [(PInv.leaders hP).2 _ hT hn] at he'
      simp [ent] at he'
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hlne
  have hlen0 : σ.len0 e.term < p := by
    apply Nat.lt_of_not_le
    intro hc
    have := ((PInv.leaders hP).1 _ _ hℓ).2.2.2.2.2.1 p hp1 hc
    rw [termAt_of_ent he'] at this; omega
  obtain ⟨_, k, pc, q, hcm, _, hk, _⟩ := hP.2.2.2.2.2.2.2.2.2.2.2.2.2 e.term p e hlne hlen0 he' hk
  have hlc : lastCfgIdx ((σ.llog e.term).take (p - 1)) =
      lastCfgIdx ((σ.srv i).log.take (p - 1)) :=
    (lastCfgIdx_agree _ _ _ (agree_mono hag (by omega))).symm
  have hTi : e.term ≤ (σ.srv i).term := by
    have := (hP.2.2.2.2.2.2.2.2.2.2.2.1 i hi').2 p hp1 hpl
    rw [show termAt (σ.log i) p = e.term from termAt_of_ent he] at this
    exact this
  obtain ⟨e2, he2⟩ := proto.ent_isSome (σ.srv i).log (lastCfgIdx ((σ.srv i).log.take (p - 1)))
    (by omega) (by omega)
  have he2' : ent (σ.llog e.term) (lastCfgIdx ((σ.srv i).log.take (p - 1))) = some e2 := by
    rw [← agree_ent hag (by omega)]; exact he2
  ihave ⟨Hh, #Hc⟩ := H_commit_get γ σ _ k pc hcm $$ Hh
  ihave ⟨Hh, #Hle⟩ := H_llog_get γ σ _ _ e2 he2' $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  iright; iexists e.term, k, pc, e2
  isplitr; · ipureintro; exact ⟨hTi, by rw [← hlc]; exact hk, he2⟩
  isplitr; · iexact Hc
  iexact Hle

/-! ## Committed indexes of a server's log (`cmtIdx`, review T1-1) -/

omit hRB in
/-- Index `0` is committed. -/
theorem cmtIdx_zero (T : Nat) (L : RLog) : ⊢ cmtIdx (GF := GF) γ T L 0 := by
  unfold cmtIdx
  ileft; ipureintro; rfl

omit hRB in
/-- A later term, and a log with the same entry at `k` (an append, a truncation above `k`). -/
theorem cmtIdx_mono (T T2 : Nat) (L L2 : RLog) (k : Nat) (hT : T ≤ T2)
    (hL : ent L2 k = ent L k) :
    cmtIdx (GF := GF) γ T L k ⊢ cmtIdx γ T2 L2 k := by
  unfold cmtIdx
  iintro (%h | ⟨%T', %k', %p', %e, %h, #Hc, #Hl⟩)
  · ileft; ipureintro; exact h
  · iright; iexists T', k', p', e
    isplitr; · ipureintro; exact ⟨Nat.le_trans h.1 hT, h.2.1, by rw [hL]; exact h.2.2⟩
    isplitr; · iexact Hc
    iexact Hl

/-- A server's durable prefix is committed (`IDur`: a recorded commit of the durable term
`≤ s.term` covers it, its leader log agrees with the server's log there): the source of
`committedIndex` when the commit index reaches the latest configuration, and at
`installSnapshot` (`committedIndex = reqConfigurationIndex ≤ s ≤ dur`). -/
theorem cmtIdx_dur (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (k : Nat)
    (hk : k ≤ s.dur.1) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢ |={E}=> srvOwn γ i s ∗ cmtIdx γ s.term s.log k := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  unfold cmtIdx
  by_cases hk0 : k = 0
  · isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    isplitl [Ho]; · iexact Ho
    ileft; ipureintro; exact hk0
  rcases ((PInv.dur hP) i hi').1 with h0 | ⟨hT, ⟨k', p', hk', hcm⟩, hag⟩
  · exfalso; omega
  have hkl : k ≤ (σ.srv i).log.length := by
    have : (σ.srv i).dur.1 ≤ (σ.srv i).log.length := hag.1; omega
  obtain ⟨e, he⟩ := proto.ent_isSome (σ.srv i).log k (by omega) hkl
  have he' : ent (σ.llog (σ.srv i).dur.2) k = some e := by
    rw [← agree_ent hag hk]; exact he
  ihave ⟨Hh, #Hc⟩ := H_commit_get γ σ _ k' p' hcm $$ Hh
  ihave ⟨Hh, #Hle⟩ := H_llog_get γ σ _ k e he' $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  iright; iexists (σ.srv i).dur.2, k', p', e
  isplitr; · ipureintro; exact ⟨hT, by omega, he⟩
  isplitr; · iexact Hc
  iexact Hle

/-- **The committed index's entry is the committed log's** (`ICommits`: a recorded commit's prefix
is in `C`). -/
theorem cmtIdx_CIdx (E : CoPset) (hE : ↑gprotN ⊆ E) (T : Nat) (L : RLog) (k : Nat) :
    Inv (GF := GF) γ ∗ cmtIdx γ T L k ⊢ |={E}=>
      ⌜k = 0⌝ ∨ ∃ e, ⌜ent L k = some e⌝ ∗ CIdx γ k e := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody cmtIdx
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hc⟩
  icases Hc with (%h | ⟨%T', %k', %p', %e, %h, #Hc, #Hl⟩)
  · isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    ileft; ipureintro; exact h
  · ihave ⟨Hh, %hc⟩ := H_commit_lookup γ σ T' k' p' $$ [Hh]
    · isplitl [Hh]; iexact Hh; iexact Hc
    ihave ⟨Hh, %hl⟩ := H_llog_lookup γ σ T' k e $$ [Hh]
    · isplitl [Hh]; iexact Hh; iexact Hl
    have hag := ((PInv.commits hg.1).1 T' k' p' hc).2.2
    have hC : ent σ.C k = some e := by rw [agree_ent hag h.2.1]; exact hl
    ihave ⟨Hh, #HC⟩ := H_C_get γ σ k e hC $$ Hh
    isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    iright; iexists e
    isplitr; · ipureintro; exact h.2.2
    iexact HC

/-- **The leader log of the server's term extends its log up to a committed index** (`ILC` on the
commit of a term `≤ s.term`, log matching on the server's log): an entry `e` at `j ≤ k` of the
leader log of `s.term` (an `AppendEntries` of `s.term`, `aeValid`) is the server's entry at `j`; so a
valid `AppendEntries` of the server's term truncates its log only above `k`
(`appendEntries`' `DeleteRange` and the rollback of `configurations.latest` to `committed`). -/
theorem cmtIdx_llog (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (k j : Nat)
    (e : Entry) (hj : j ≤ k) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ cmtIdx γ s.term s.log k ∗ llogIdx γ s.term j e ⊢ |={E}=>
      srvOwn γ i s ∗ ⌜ent s.log j = some e⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, #Hc, #Hj⟩
  ihave ⟨Hh, %hj⟩ := H_llog_lookup γ σ s.term j e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hj
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hj1 := ent_pos hj
  unfold cmtIdx
  icases Hc with (%h0 | ⟨%T', %k', %p', %e', %h, #Hcm, #Hl⟩)
  · exfalso; omega
  ihave ⟨Hh, %hcm⟩ := H_commit_lookup γ σ T' k' p' $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hcm
  ihave ⟨Hh, %hl⟩ := H_llog_lookup γ σ T' k e' $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  ipureintro
  have hk1 : 1 ≤ k := by omega
  have hkl : k ≤ (σ.srv i).log.length := ent_le_length h.2.2
  have a1 : agree (σ.srv i).log (σ.llog e'.term) k := by
    have := ((PInv.logs hP).1 i hi').1 k hk1 hkl
    rw [show termAt (σ.log i) k = e'.term from termAt_of_ent h.2.2] at this
    exact this
  have a2 : agree (σ.llog T') (σ.llog e'.term) k := by
    have := (PInv.logs hP).2.1 T' k hk1 (ent_le_length hl)
    rw [termAt_of_ent hl] at this
    exact this
  have hag : agree (σ.srv i).log (σ.llog T') k := agree_trans a1 (agree_symm a2)
  have hTT : ent (σ.llog (σ.srv i).term) j = ent (σ.llog T') j := by
    rcases Nat.lt_or_eq_of_le h.1 with hlt | heq
    · have hc := (PInv.commits hP).1 T' k' p' hcm
      have hlne : σ.leader (σ.srv i).term ≠ none := by
        intro hn
        by_cases hT1 : (σ.srv i).term = 1
        · have := hc.1.1
          have h0 : T' = 0 := by omega
          rw [h0, (PInv.gen hP).2.2.2.2.2.2.1] at this
          exact this rfl
        · rw [(PInv.leaders hP).2 _ hT1 hn] at hj
          simp [ent] at hj
      have := hP.2.2.2.2.2.2.2.1 T' k' p' hc.1 hc.2.1 _ hlt hlne
      unfold lacks at this
      exact agree_ent (Classical.not_not.mp this).2 (by omega)
    · rw [heq]
  show ent (σ.srv i).log j = some e
  rw [agree_ent hag (by omega), ← hTT]; exact hj

/-- **The committed prefix of a server's log** (`proto.dur_C`, `proto.snap_cfg`): the committed log
extends the server's durable prefix; so the latest configuration at or below any `x ≤ dur` is the
committed log's (the snapshot's configuration, `takeSnapshot`). -/
theorem srvOwn_CLb (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢ |={E}=> srvOwn γ i s ∗ CLb γ (s.log.take s.dur.1) := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  ihave ⟨Hh, #HC⟩ := H_C_lb γ σ $$ Hh
  have hd : (σ.srv i).dur.1 ≤ (σ.srv i).log.length := dur_le_log σ i hP hi'
  have hCd : (σ.srv i).dur.1 ≤ σ.C.length := by
    by_cases h0 : (σ.srv i).dur.1 = 0
    · omega
    · exact (dur_C σ i (σ.srv i).dur.1 hP hi' (by omega) (Nat.le_refl _)).1
  have ha : agree (σ.srv i).log σ.C (σ.srv i).dur.1 :=
    proto.agree_of_ent hd hCd (fun x h1 h2 => (dur_C σ i x hP hi' h1 h2).2.symm)
  have hpre : (σ.srv i).log.take (σ.srv i).dur.1 <+: σ.C := by
    rw [ha.2.2]; exact List.take_prefix _ _
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  have hle : CLb (GF := GF) γ σ.C ⊢ CLb γ ((σ.srv i).log.take (σ.srv i).dur.1) := by
    unfold CLb; exact monoListLbOwn_le _ hpre
  iapply hle $$ HC

/-- A lower bound of the committed log bounds it by its prefixes too. -/
theorem CLb_take (L : RLog) (n : Nat) : CLb (GF := GF) γ L ⊢ CLb γ (L.take n) := by
  unfold CLb
  exact monoListLbOwn_le _ (List.take_prefix n L)

/-! ## A leader's own log -/

/-- `llogPre` is the leader log's entries, one `llogIdx` per index. -/
theorem llogPre_eq (T : Nat) (L : RLog) :
    llogPre (GF := GF) γ T L ⊣⊢ [∗list] k ↦ e ∈ L, llogIdx γ T (k + 1) e := by
  unfold llogPre; exact .rfl

/-- The leader of its current term: its log is a prefix of (is) its leader log. -/
theorem llogPre_leader (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ leaderIs γ s.term i ⊢ |={E}=>
      srvOwn γ i s ∗ llogPre γ s.term s.log := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho, #Hl⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hLL : (σ.srv i).log = σ.llog (σ.srv i).term := leader_log σ i hP hi' hl
  ihave ⟨Hh, #Hp⟩ := H_llog_get_list γ σ (σ.srv i).term (σ.srv i).log (fun j => j + 1)
    (by intro j e hj; rw [ent_succ, ← hLL]; exact hj) $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  unfold llogPre; iexact Hp

/-- (review T1-4) **A server's log is a prefix of the leader log of its last entry's term** (`LMok`;
`[]` when the log is empty): the candidate's election log as a persistent fact (`electSelf`,
`runCandidate`, `leader_votes_agree`). -/
theorem llogPre_srv (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ⊢ |={E}=> srvOwn γ i s ∗ llogPre γ (lastTerm s.log) s.log := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ho⟩
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_peek γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  ihave Hs := Hcl $$ Hi
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hpre : ∀ (j : Nat) (e : Entry), (σ.srv i).log[j]? = some e →
      ent (σ.llog (lastTerm (σ.srv i).log)) (j + 1) = some e := by
    intro j e hj
    have hlen : j + 1 ≤ (σ.srv i).log.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; omega
    have a : agree (σ.srv i).log (σ.llog (termAt (σ.srv i).log (σ.srv i).log.length))
        (σ.srv i).log.length := ((PInv.logs hP).1 i hi').1 (σ.srv i).log.length (by omega) (Nat.le_refl _)
    unfold lastTerm
    rw [← agree_ent a hlen, ent_succ]; exact hj
  ihave ⟨Hh, #Hp⟩ := H_llog_get_list γ σ (lastTerm (σ.srv i).log) (σ.srv i).log (fun j => j + 1)
    hpre $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  isplitl [Ho]; · iexact Ho
  unfold llogPre; iexact Hp

/-- A prefix of a known prefix of the leader log is one. -/
theorem llogPre_take (T : Nat) (L : RLog) (n : Nat) :
    llogPre (GF := GF) γ T L ⊢ llogPre γ T (L.take n) := by
  unfold llogPre
  have h : ([∗list] k ↦ e ∈ L, llogIdx (GF := GF) γ T (k + 1) e) ⊣⊢
      [∗list] k ↦ e ∈ L.take n ++ L.drop n, llogIdx (GF := GF) γ T (k + 1) e := by
    rw [List.take_append_drop]; exact .rfl
  exact h.1.trans (BigSepL.bigSepL_append.1.trans sep_elim_left)

/-- An entry of a known prefix of the leader log is the leader log's. -/
theorem llogPre_idx (T : Nat) (L : RLog) (k : Nat) (e : Entry) (h : ent L k = some e) :
    llogPre (GF := GF) γ T L ⊢ llogIdx γ T k e := by
  unfold llogPre
  have hk := ent_pos h
  have h' : L[k - 1]? = some e := by rw [← ent_eq_getElem? _ _ hk]; exact h
  have := BigSepL.bigSepL_lookup (Φ := fun k e => llogIdx (GF := GF) γ T (k + 1) e) h'
  rw [show k - 1 + 1 = k by omega] at this
  exact this

/-- (stage 4, hub L2) A configuration entry of a leader log has valid voters (`proto.ICfgOk`):
`commitment.recalculate`'s quorum over the commitment's configuration. -/
theorem llogIdx_cfgValid (E : CoPset) (hE : ↑gprotN ⊆ E) (T k : Nat) (e : Entry)
    (hk : e.kind = kConfig) :
    Inv (GF := GF) γ ∗ llogIdx γ T k e ⊢ |={E}=> ⌜cfgValid γ.srvs (γ.cv e.data)⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hl⟩
  ihave ⟨Hh, %he⟩ := H_llog_lookup γ σ T k e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  have h := (PInv.logs hg.1).2.2.2.2 T k e he hk
  rw [← hg.2.1, ← hg.2.2.2.1]; exact h

end cfg

end gprot
end github_com.hashicorp.raft

end Perennial
