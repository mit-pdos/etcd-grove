/-
(hraft_robust R2, R1 §1.4 step 2) **The wrapper laws**: gprot's laws on the main goroutine's state
(`srvOwn` and the couples, now in `srvDurInv`), restated over the views (`srvV`/`srvVP`, `stVS`,
`termV`, `cidxV`) and the crash invariant, as crash-token updates (`|NC={E}=>`, the mask containing
`↑gprotN ∪ ↑durN`). A site that applied `L` now applies `L_R`:
`imod (L_R …) $$ [Hs …] Hnc with ⟨Hnc, …⟩` (or `iapply`, with `Hnc` from a store's or channel's
atomic update, `wp_atomic_nc` or `wp_ncfupd`).

* **No change of the state** (`*_R` of the fact laws), and the in-memory commit learnt (`dur` grows).
* **The atomics' cells**: the term step (`setTerm_R`/`electTerm_R`, the pending `tp` fired at the
  `currentTerm` store), the commit index (`setCidx_R`), the readers' agreements and bounds.
* **The stores' atomic updates** (R1 §2.2's table): generic builders (`logWrite_au`, `logDelete_au`,
  `logRead_au`, `stableWrite_au`, `stableRead_au`, `snapWrite_au`, `snapRead_au`) whose
  continuation gets the opened core (`durCore`) and re-establishes it, and the commit of each
  durable write that fires a step (`storeLogs_app_win`, `storeLogs_cfg_win`, `storeLogs_fstore_win`,
  `deleteRange_trunc_win`, `setUint64_term_win`, `set_voteCand_win`, `setUint64_vote_win`): both
  arguments of the write's contract, its window (`logWin`/`stWin`) and its atomic update.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Crash

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section crashLaws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

variable (γ : GNames) (rc : RCtx GF) (i : SID)

/-- The least `m < n` with `P m`, if any. -/
theorem crash_least (P : Nat → Prop) (n : Nat) :
    (∀ m, m < n → ¬ P m) ∨ ∃ m, m < n ∧ P m ∧ ∀ j, j < m → ¬ P j := by
  induction n with
  | zero => exact Or.inl (fun m h => absurd h (Nat.not_lt_zero _))
  | succ n ih =>
    rcases ih with h | ⟨m, hm, hP, hj⟩
    · rcases Classical.em (P n) with hn | hn
      · exact Or.inr ⟨n, by omega, hn, fun j hj' => h j hj'⟩
      · refine Or.inl (fun m hm => ?_)
        rcases Nat.lt_or_ge m n with h1 | h1
        · exact h m h1
        · rw [show m = n by omega]; exact hn
    · exact Or.inr ⟨m, by omega, hP, hj⟩

/-! ### The pending install's prefix through a log step -/

theorem prevMatch_append (L es : RLog) (x st : Nat) (h : prevMatch L x st) : prevMatch (L ++ es) x st := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨by simp; omega, by rw [termAt_append_left _ _ _ h1]; exact h2⟩

theorem prevMatch_take (L : RLog) (n x st : Nat) (hx : x ≤ n) (h : prevMatch L x st) :
    prevMatch (L.take n) x st := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨by simp; omega, by rw [termAt_take _ _ _ hx]; exact h2⟩

/-- (R2) The pending-install facts through a log step that keeps the durable prefix. -/
theorem q2_step (lo : Nat) (lat : SnapLatest) (pend : Option (Nat × Nat × GoString)) (dp : Option DiscPend)
    (L L' : RLog) (d d' : Nat) (hd : d ≤ d')
    (hL : ∀ x st, x ≤ d → prevMatch L x st → prevMatch L' x st)
    (h : (∀ dd, dp = some dd → lo ≤ dd.x) ∧
      (∀ x st id, pend = some (x, st, id) → (∃ ℓ, dp = some ⟨x, st, ℓ⟩) ∨ (prevMatch L x st ∧ x ≤ d)) ∧
      lo ≤ latIdxD lat + 1) :
    (∀ dd, dp = some dd → lo ≤ dd.x) ∧
      (∀ x st id, pend = some (x, st, id) → (∃ ℓ, dp = some ⟨x, st, ℓ⟩) ∨ (prevMatch L' x st ∧ x ≤ d')) ∧
      lo ≤ latIdxD lat + 1 := by
  refine ⟨h.1, fun x st id hp => ?_, h.2.2⟩
  rcases h.2.1 x st id hp with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hL x st h2 h1, by omega⟩

/-! ## Masks -/

theorem crash_hE_dur {E : CoPset} (hE : ↑gprotN ∪ ↑durN ⊆ E) : (↑durN : CoPset) ⊆ E :=
  fun x hx => hE x (Iris.Std.LawfulSet.mem_union.2 (Or.inr hx))

theorem crash_gprot_not_dur : (↑gprotN : CoPset) ⊆ ⊤ \ ↑durN := by
  unfold gprotN durN raftN; solve_ndisj

theorem crash_hE_gprot {E : CoPset} (hE : ↑gprotN ∪ ↑durN ⊆ E) : (↑gprotN : CoPset) ⊆ E \ ↑durN := by
  intro x hx
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨hE x (Iris.Std.LawfulSet.mem_union.2 (Or.inl hx)), ?_⟩
  have h := crash_gprot_not_dur x hx
  rw [Iris.Std.LawfulSet.mem_diff] at h
  exact h.2

/-! ## Generic: a step of gprot's halves with the main goroutine's view -/

/-- (R2) The main goroutine's plain view agrees with the crash state (no pending step). -/
theorem durCore_srvV_agree (X : SrvDur) (s : SState) :
    durCore γ rc i X ∗ srvV rc s ⊢ durCore γ rc i X ∗ srvV rc s ∗ ⌜X.s = s ∧ X.tp = none ∧ X.dp = none⌝ :=
  durCore_srvVP_agree γ rc i X s none none

theorem durStores_with (X : SrvDur) (s : SState) (tp : Option TermPend) :
    durStores γ rc i { X with s := s, tp := tp } = durStores γ rc i X := rfl

theorem dpRes_dur (s : SState) (d : Nat × Nat) (dp : Option DiscPend) :
    dpRes (GF := GF) γ i { s with dur := d } dp = dpRes γ i s dp := by
  cases dp <;> rfl

/-- (R2) **A look at gprot's `srvOwn`** with the main goroutine's view, the state unchanged. -/
theorem durPeek {E : CoPset} (hE : ↑durN ⊆ E) (s : SState) (tp : Option TermPend)
    (dp : Option DiscPend) (P Q : IProp GF) :
    srvDurInv γ rc i ∗ srvVP rc s tp dp ∗ P ∗
      (srvOwn γ i s -∗ P -∗ |={E \ ↑durN}=> srvOwn γ i s ∗ Q) ⊢
      |NC={E}=> srvVP rc s tp dp ∗ Q := by
  iintro ⟨#Hi, Hv, HP, Hf⟩ Hnc
  imod (durOpen γ rc i hE) $$ Hi Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hv]
  · iframe
  obtain ⟨hs, -, -⟩ := Hag
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hc⟩
  ihave Ho : srvOwn γ i s $$ [Ho]
  · rw [← hs]; iexact Ho
  imod Hf $$ Ho HP with ⟨Ho, HQ⟩
  imod Hcl $$ %X [Ho Hc] Hs with -
  · iunfold durCore; rw [hs]; iframe
  imodintro
  iframe

/-- (R2) **An in-memory step of the main goroutine**: only the durable prefix `dur` changes, and
only up (what the commit laws do); the couplings are unchanged. -/
theorem durStepV {E : CoPset} (hE : ↑durN ⊆ E) (s : SState) (tp : Option TermPend)
    (dp : Option DiscPend) (P : IProp GF) (Q : SState → IProp GF) :
    srvDurInv γ rc i ∗ srvVP rc s tp dp ∗ P ∗
      (srvOwn γ i s -∗ durView γ i (1 : Qp).half s.dur.1 -∗ P -∗
        |={E \ ↑durN}=> ∃ d : Nat × Nat, srvOwn γ i { s with dur := d } ∗
          durView γ i (1 : Qp).half d.1 ∗ ⌜s.dur.1 ≤ d.1⌝ ∗ Q { s with dur := d }) ⊢
      |NC={E}=> ∃ d : Nat × Nat, srvVP rc { s with dur := d } tp dp ∗ Q { s with dur := d } := by
  iintro ⟨#Hd, Hv, HP, Hf⟩ Hnc
  imod (durOpen γ rc i hE) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hv]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  imod Hf $$ Ho Hdv HP with ⟨%d, Ho, Hdv, %hle, HQ⟩
  unfold srvVP
  imod (ghostVar_update_halves ({ s with dur := d }, tp, dp) rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  rw [← dpRes_dur γ i s d dp]
  rw [← durStores_with γ rc i X { s with dur := d } tp]
  imod Hcl $$ %({ X with s := { s with dur := d }, tp := tp }) [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp Hla] Hs with -
  · iunfold durCore
    dsimp only
    try rw [hdp]
    iframe
    ipureintro
    exact ⟨hlo, hlc, hvm, htd, by have := hci.1; omega, ⟨q2_step _ _ _ _ _ _ _ _ hle (fun x st _ h => h) hci.2.1, hci.2.2⟩⟩
  imodintro
  iframe Hnc
  iexists d
  iframe

/-- (R2) `durPeek` at the main goroutine's plain view. -/
theorem durPeekV {E : CoPset} (hE : ↑durN ⊆ E) (s : SState) (P Q : IProp GF) :
    srvDurInv γ rc i ∗ srvV rc s ∗ P ∗
      (srvOwn γ i s -∗ P -∗ |={E \ ↑durN}=> srvOwn γ i s ∗ Q) ⊢
      |NC={E}=> srvV rc s ∗ Q :=
  durPeek γ rc i hE s none none P Q

/-- (R2) `durStepV` at the main goroutine's plain view. -/
theorem durStepVV {E : CoPset} (hE : ↑durN ⊆ E) (s : SState) (P : IProp GF) (Q : SState → IProp GF) :
    srvDurInv γ rc i ∗ srvV rc s ∗ P ∗
      (srvOwn γ i s -∗ durView γ i (1 : Qp).half s.dur.1 -∗ P -∗
        |={E \ ↑durN}=> ∃ d : Nat × Nat, srvOwn γ i { s with dur := d } ∗
          durView γ i (1 : Qp).half d.1 ∗ ⌜s.dur.1 ≤ d.1⌝ ∗ Q { s with dur := d }) ⊢
      |NC={E}=> ∃ d : Nat × Nat, srvV rc { s with dur := d } ∗ Q { s with dur := d } :=
  durStepV γ rc i hE s none none P Q

/-- (R2) The request's entries agree with the log below a committed index `k` of the current term
(`cmtIdx_llog`, entry by entry). -/
theorem crash_ents_match {E : CoPset} (hE : ↑gprotN ⊆ E) (s : SState) (prev : Nat) (ents : RLog) (k n : Nat) (hn : n = 0 ∨ prev + n ≤ k)
    (hn2 : n ≤ ents.length) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ cmtIdx γ s.term s.log k ∗
      ([∗list] j ↦ e ∈ ents, llogIdx γ s.term (prev + 1 + j) e) ⊢ |={E}=>
      srvOwn γ i s ∗ ⌜∀ m, m < n → ent s.log (prev + m + 1) = ents[m]?⌝ := by
  induction n with
  | zero =>
    iintro ⟨-, Ho, -, -⟩
    imodintro; iframe; ipureintro; intro m hm; omega
  | succ n ih =>
    iintro ⟨#HI, Ho, #Hc, #Hl⟩
    imod (ih (by omega) (by omega)) $$ [Ho] with ⟨Ho, %h⟩
    · iframe; iframe #
    obtain ⟨e, he⟩ : ∃ e, ents[n]? = some e := ⟨ents[n]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    ihave #He := BigSepL.bigSepL_lookup (Φ := fun j e => llogIdx (GF := GF) γ s.term (prev + 1 + j) e) he $$ Hl
    imod (gprot.cmtIdx_llog γ _ hE i s k (prev + 1 + n) e (by omega)) $$ [HI Ho Hc He] with ⟨Ho, %hen⟩
    · iframe #; try iframe
    imodintro
    iframe
    ipureintro
    intro m hm
    rcases Nat.lt_or_ge m n with h1 | h1
    · exact h m h1
    · rw [show m = n by omega, he, show prev + n + 1 = prev + 1 + n by omega]; exact hen

/-! ## The fact laws (the state unchanged) -/

section facts
variable {E : CoPset} (hE : ↑gprotN ∪ ↑durN ⊆ E) (s : SState)
include hE

theorem srvOwn_facts_R :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={E}=> srvV rc s ∗ isSrv γ i ∗
      ⌜(s.log = [] ∨ ent s.log 1 = some γ.g) ∧ s.dur.1 ≤ s.log.length ∧ s.cidx ≤ s.dur.1 ∧
        s.vterm ≤ s.term ∧ (s.log ≠ [] → 1 ≤ s.term) ∧ s.term < 2 ^ 62 ∧ s.log.length < 2 ^ 62 ∧
        (∀ k e, ent s.log k = some e → e.kind = kConfig → cfgValid γ.srvs (γ.cv e.data)) ∧
        (∀ k e, ent s.log k = some e →
          e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier ∨ e.kind = kConfig)⌝ := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.srvOwn_facts γ _ (crash_hE_gprot hE) i s) $$ [HI Ho]
  iframe HI Ho

theorem srvOwn_durLb_R :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={E}=> srvV rc s ∗ durLb γ i s.dur.1 := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.srvOwn_durLb γ _ (crash_hE_gprot hE) i s) $$ [HI Ho]
  iframe HI Ho

theorem durLb_le_R (k : Nat) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ durLb γ i k ⊢ |NC={E}=> srvV rc s ∗ ⌜k ≤ s.dur.1⌝ := by
  iintro ⟨#HI, #Hd, Hv, HP⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.durLb_le γ _ (crash_hE_gprot hE) i s k) $$ [HI Ho HP]
  iframe HI Ho; iexact HP

theorem srvOwn_vcand_R :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢
      |NC={E}=> srvV rc s ∗ ⌜0 < s.vterm → s.vcand ∈ γ.srvs⌝ := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.srvOwn_vcand γ _ (crash_hE_gprot hE) i s) $$ [HI Ho]
  iframe HI Ho

theorem vote_again_R (hv : 0 < s.vterm) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={E}=> srvV rc s ∗ voteIs γ i s.vterm s.vcand := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.vote_again γ _ (crash_hE_gprot hE) i s hv) $$ [HI Ho]
  iframe HI Ho

theorem becomeLeader_upd_R (Q : List SID) (hQ : isQuorumOf (cfgOfC γ.cv s.log) Q) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ candIs γ i s.term s.log.length (lastTerm s.log) ∗
      ([∗list] j ∈ Q, voteIs γ j s.term i) ∗ ccfgOwn γ i s.term 0 ∗ ccfgOwn γ i s.term 0 ⊢
      |NC={E}=> srvV rc s ∗ leaderIs γ s.term i ∗ len0Is γ s.term s.log.length ∗
        ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ ccfgOwn γ i s.term (lastCfgIdx s.log) := by
  iintro ⟨#HI, #Hd, Hv, H1, H2, H3, H4⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.becomeLeader_upd γ _ (crash_hE_gprot hE) i s Q hQ)
  iframe
  iexact HI

theorem installCfg_upd_R (p : Nat) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ leaderIs γ s.term i ∗ ccfgOwn γ i s.term p ∗
      ccfgOwn γ i s.term p ⊢
      |NC={E}=> srvV rc s ∗ ccfgOwn γ i s.term (lastCfgIdx s.log) ∗
        ccfgOwn γ i s.term (lastCfgIdx s.log) := by
  iintro ⟨#HI, #Hd, Hv, H1, H2, H3⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.installCfg_upd γ _ (crash_hE_gprot hE) i s p)
  iframe
  iexact HI

theorem ackLeader_R :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ leaderIs γ s.term i ⊢
      |NC={E}=> srvV rc s ∗ ackIs γ i s.term s.log.length := by
  iintro ⟨#HI, #Hd, Hv, HP⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.ackLeader γ _ (crash_hE_gprot hE) i s) $$ [HI Ho HP]
  iframe HI Ho; iexact HP

theorem ackFollower_R (prev pt : Nat) (ents : RLog) (lci : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents ents.length) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ aeValid γ s.term prev pt ents lci ⊢
      |NC={E}=> srvV rc s ∗ ackIs γ i s.term (prev + ents.length) := by
  iintro ⟨#HI, #Hd, Hv, HP⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.ackFollower γ _ (crash_hE_gprot hE) i s prev pt ents lci hpre) $$ [HI Ho HP]
  iframe HI Ho; iexact HP

theorem append_bound_R (n : Nat) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ receipt n ⊢
      |NC={E}=> srvV rc s ∗ receipt n ∗ ⌜s.log.length + n < 2 ^ 62⌝ := by
  iintro ⟨#HI, #Hd, Hv, HP⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.append_bound γ _ (crash_hE_gprot hE) i s n) $$ [HI Ho HP]
  iframe HI Ho; iexact HP

theorem llogIdx_leader_R (k : Nat) (e : Entry) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ leaderIs γ s.term i ∗ llogIdx γ s.term k e ⊢
      |NC={E}=> srvV rc s ∗ ⌜ent s.log k = some e⌝ := by
  iintro ⟨#HI, #Hd, Hv, H1, H2⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.llogIdx_leader γ _ (crash_hE_gprot hE) i s k e)
  iframe
  iexact HI

theorem applied_C_R (x : Nat) (e : Entry) (hx : 1 ≤ x ∧ x ≤ s.dur.1) (he : ent s.log x = some e) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={E}=> srvV rc s ∗ CIdx γ x e := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.applied_C γ _ (crash_hE_gprot hE) i s x e hx he) $$ [HI Ho]
  iframe HI Ho

theorem cfgPrevCommitted_R (p : Nat) (e : Entry) (he : ent s.log p = some e) (hk : e.kind = kConfig) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢
      |NC={E}=> srvV rc s ∗ cmtIdx γ s.term s.log (lastCfgIdx (s.log.take (p - 1))) := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.cfgPrevCommitted γ _ (crash_hE_gprot hE) i s p e he hk) $$ [HI Ho]
  iframe HI Ho

theorem cmtIdx_dur_R (k : Nat) (hk : k ≤ s.dur.1) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={E}=> srvV rc s ∗ cmtIdx γ s.term s.log k := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.cmtIdx_dur γ _ (crash_hE_gprot hE) i s k hk) $$ [HI Ho]
  iframe HI Ho

theorem cmtIdx_llog_R (k j : Nat) (e : Entry) (hj : j ≤ k) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ cmtIdx γ s.term s.log k ∗ llogIdx γ s.term j e ⊢
      |NC={E}=> srvV rc s ∗ ⌜ent s.log j = some e⌝ := by
  iintro ⟨#HI, #Hd, Hv, H1, H2⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.cmtIdx_llog γ _ (crash_hE_gprot hE) i s k j e hj)
  iframe
  iexact HI

theorem srvOwn_CLb_R :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={E}=> srvV rc s ∗ CLb γ (s.log.take s.dur.1) := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.srvOwn_CLb γ _ (crash_hE_gprot hE) i s) $$ [HI Ho]
  iframe HI Ho

theorem llogPre_leader_R :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ leaderIs γ s.term i ⊢
      |NC={E}=> srvV rc s ∗ llogPre γ s.term s.log := by
  iintro ⟨#HI, #Hd, Hv, HP⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.llogPre_leader γ _ (crash_hE_gprot hE) i s) $$ [HI Ho HP]
  iframe HI Ho; iexact HP

theorem llogPre_srv_R :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={E}=> srvV rc s ∗ llogPre γ (lastTerm s.log) s.log := by
  iintro ⟨#HI, #Hd, Hv⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.llogPre_srv γ _ (crash_hE_gprot hE) i s) $$ [HI Ho]
  iframe HI Ho

theorem srvOwn_now_R (s0 : Snap) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ histLb γ s0 ⊢ |NC={E}=> srvV rc s ∗
      ∃ s', histLb γ s' ∗ ⌜snapLe s0 s' ∧ s'.term i = s.term ∧ s'.dur i = s.dur.1⌝ := by
  iintro ⟨#HI, #Hd, Hv, HP⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.srvOwn_now γ _ (crash_hE_gprot hE) i s s0) $$ [HI Ho HP]
  iframe HI Ho; iexact HP

theorem srvOwn_now_leader_R (s0 : Snap) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ leaderIs γ s.term i ∗ histLb γ s0 ⊢ |NC={E}=> srvV rc s ∗
      ∃ s', histLb γ s' ∗
        ⌜snapLe s0 s' ∧ s'.term i = s.term ∧ s'.dur i = s.dur.1 ∧ s'.llen s.term = s.log.length⌝ := by
  iintro ⟨#HI, #Hd, Hv, H1, H2⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.srvOwn_now_leader γ _ (crash_hE_gprot hE) i s s0)
  iframe
  iexact HI

theorem truncate_gt_dur_R (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents j ∧ j < ents.length ∧
      prev + 1 + j ≤ s.log.length ∧ termAt s.log (prev + 1 + j) ≠ termAt ents (j + 1)) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ aeValid γ s.term prev pt ents lci ⊢
      |NC={E}=> srvV rc s ∗ ⌜s.dur.1 < prev + 1 + j⌝ := by
  iintro ⟨#HI, #Hd, Hv, HP⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  iapply (gprot.truncate_gt_dur γ _ (crash_hE_gprot hE) i s prev pt ents lci j hpre) $$ [HI Ho HP]
  iframe HI Ho; iexact HP

/-- (R2, for R4a's appendEntries) **A valid request matches the log up to the durable prefix**: with its
previous entry matched, its entries agree with the log up to `dur` (a mismatch below `dur` would be a
truncation of a durable entry: `truncate_gt_dur`). -/
theorem aeValid_match_dur_R (prev pt : Nat) (ents : RLog) (lci : Nat) (hp : prevMatch s.log prev pt) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ aeValid γ s.term prev pt ents lci ⊢
      |NC={E}=> srvV rc s ∗ ⌜matchedUpTo s.log prev ents (Min.min ents.length (s.dur.1 - prev)) ∧
        ∀ m, m < Min.min ents.length (s.dur.1 - prev) → ent s.log (prev + m + 1) = ents[m]?⌝ := by
  iintro ⟨#HI, #Hd, Hv, #Hae⟩
  iapply (durPeekV γ rc i (crash_hE_dur hE) s iprop(True) _)
  iframe Hd Hv
  isplitl []
  · itrivial
  iintro Ho -
  imod (gprot.srvOwn_facts γ _ (crash_hE_gprot hE) i s) $$ [HI Ho] with ⟨Ho, -, %hf⟩
  · iframe #; try iframe
  have hdl := hf.2.1
  imod (gprot.cmtIdx_dur γ _ (crash_hE_gprot hE) i s s.dur.1 (Nat.le_refl _)) $$ [HI Ho] with ⟨Ho, #Hcm⟩
  · iframe #; try iframe
  ihave #Hae' := Hae
  iunfold aeValid at Hae'
  icases Hae' with ⟨-, -, #Hents, -⟩
  imod (crash_ents_match γ i (crash_hE_gprot hE) s prev ents s.dur.1 (Min.min ents.length (s.dur.1 - prev))
    (by omega) (by omega)) $$ [HI Ho Hcm Hents] with ⟨Ho, %hents⟩
  · iframe #; try iframe
  rcases crash_least (fun m => termAt s.log (prev + 1 + m) ≠ termAt ents (m + 1))
      (Min.min ents.length (s.dur.1 - prev)) with hall | ⟨m, hm, hne, hmin⟩
  · imodintro
    iframe
    ipureintro
    refine ⟨⟨by omega, fun j' hj' => ⟨by omega, ?_⟩⟩, hents⟩
    exact Classical.byContradiction (hall j' hj')
  · have hmin' : ∀ j', j' < m → termAt s.log (prev + 1 + j') = termAt ents (j' + 1) :=
      fun j' hj' => Classical.byContradiction (hmin j' hj')
    imod (gprot.truncate_gt_dur γ _ (crash_hE_gprot hE) i s prev pt ents lci m
      ⟨hp, ⟨by omega, fun j' hj' => ⟨by omega, hmin' j' hj'⟩⟩, by omega, by omega, hne⟩)
      $$ [HI Ho Hae] with ⟨Ho, %hgt⟩
    · iframe #; try iframe
    exfalso; omega

/-! ## In-memory commits (`dur` grows) -/

theorem learnCommitLeader_R (k k' p m : Nat) (hk : k ≤ k') :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ leaderIs γ s.term i ∗ commitIs γ s.term k' p ∗
      pubOwn γ i s.term m ⊢
      |NC={E}=> ∃ d : Nat × Nat, srvV rc { s with dur := d } ∗ durLb γ i k ∗
        pubOwn γ i s.term (Max.max m k) ∗ pubIs γ s.term k ∗ ⌜d.1 = Max.max s.dur.1 k⌝ := by
  iintro ⟨#HI, #Hd, Hv, #Hl, #Hc, Hp⟩ Hnc
  imod (durStepVV γ rc i (crash_hE_dur hE) s (pubOwn γ i s.term m)
    (fun s' => iprop(durLb γ i k ∗ pubOwn γ i s.term (Max.max m k) ∗ pubIs γ s.term k ∗
      ⌜s'.dur.1 = Max.max s.dur.1 k⌝))) $$ [Hd Hv Hp] Hnc with ⟨Hnc, %d, Hv, #Hlb, Hp, #Hpub, %hd⟩
  · iframe Hd Hv Hp
    iintro Ho Hdv Hp
    imod (gprot.learnCommitLeader γ _ (crash_hE_gprot hE) i s k k' p m hk) $$ [HI Ho Hdv Hl Hc Hp]
      with ⟨%d, Ho, Hdv, #Hlb, Hp, #Hpub, %hd⟩
    · iframe #; try iframe
    imodintro
    iexists d
    iframe
    iframe #
    ipureintro
    exact ⟨by omega, hd⟩
  imodintro
  iframe Hnc
  iexists d
  iframe
  iframe #
  ipureintro
  exact hd

theorem learnCommitFollower_R (prev pt : Nat) (ents : RLog) (lci v : Nat)
    (hpre : prevMatch s.log prev pt ∧ matchedUpTo s.log prev ents ents.length ∧
      v ≤ prev + ents.length ∧ 0 < Min.min lci v) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ aeValid γ s.term prev pt ents lci ⊢
      |NC={E}=> ∃ d : Nat × Nat, srvV rc { s with dur := d } ∗ durLb γ i (Min.min lci v) ∗
        ⌜d.1 = Max.max s.dur.1 (Min.min lci v)⌝ := by
  iintro ⟨#HI, #Hd, Hv, #Hae⟩ Hnc
  imod (durStepVV γ rc i (crash_hE_dur hE) s iprop(True)
    (fun s' => iprop(durLb γ i (Min.min lci v) ∗ ⌜s'.dur.1 = Max.max s.dur.1 (Min.min lci v)⌝)))
    $$ [Hd Hv] Hnc with ⟨Hnc, %d, Hv, #Hlb, %hd⟩
  · iframe Hd Hv
    isplitl []
    · itrivial
    iintro Ho Hdv -
    imod (gprot.learnCommitFollower γ _ (crash_hE_gprot hE) i s prev pt ents lci v hpre) $$ [HI Ho Hdv Hae]
      with ⟨%d, Ho, Hdv, #Hlb, %hd⟩
    · iframe #; try iframe
    imodintro
    iexists d
    iframe
    iframe #
    ipureintro
    exact ⟨by omega, hd⟩
  imodintro
  iframe Hnc
  iexists d
  iframe
  iframe #
  ipureintro
  exact hd

end facts

/-! ## The atomics' cells -/

section cells
variable {E : CoPset} (hE : ↑gprotN ∪ ↑durN ⊆ E)
include hE

/-- (R2) **The term step at the `currentTerm` store** (inside `termCell`'s update, `E = ⊤ \ ↑termN`),
adopting `t`: the pending `tp = .set t` (recorded at `SetUint64`'s commit, `setUint64_term_au`)
fired (`setTerm_upd`, its `termOk` from `tpRes`). -/
theorem setTerm_R (s : SState) (t t0 : Nat) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvVP rc s (some (.set t)) none ∗ termV rc t0 ⊢
      |NC={E}=> srvV rc { s with term := t } ∗ termV rc t ∗ termLb γ i t := by
  iintro ⟨#HI, #Hd, Hv, Ht⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvVP_agree γ rc i X s _ _ $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_termV_agree γ rc i X t0 $$ [Hc Ht]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  have hle : s.term ≤ t := by
    unfold termDurOk at htd
    rcases htd with ⟨h, _⟩ | ⟨t', h, _, h'⟩ | ⟨h, _⟩
    · cases h
    · cases h; exact h'
    · cases h
  have hdt : uint.nat ((X.D.ints.lookup (go!"CurrentTerm" : List w8)).getD (W64 0)) = t := by
    unfold termDurOk at htd
    rcases htd with ⟨h, _⟩ | ⟨t', h, h1, _⟩ | ⟨h, _⟩
    · cases h
    · cases h; exact h1
    · cases h
  iunfold tpRes at Htp
  imod (gprot.setTerm_upd γ _ (crash_hE_gprot hE) i s t hle) $$ [HI Ho Htc Htp] with ⟨Ho, Htc, #Hlb⟩
  · iframe #; try iframe
  unfold srvVP termV
  imod (ghostVar_update_halves ({ s with term := t }, (none : Option TermPend), (none : Option DiscPend))
    rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imod (ghostVar_update_halves t rc.dur.tv _ _) $$ Htv Ht with ⟨Htv, Ht⟩
  rw [← durStores_with γ rc i X { s with term := t } none]
  imod Hcl $$ %({ X with s := { s with term := t }, tp := none }) [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Hla] Hs with -
  · iunfold durCore
    dsimp only
    try rw [hdp]
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨hlo, hlc, ?_, ?_, ⟨hci.1, hci.2.1, hci.2.2.1, (by simp), (by simp)⟩⟩
    · unfold voteMatches at hvm ⊢
      obtain ⟨h1, h2⟩ := hvm
      refine ⟨h1, ?_⟩
      rcases h2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by simp only; omega))
      · exact Or.inr (Or.inr h)
    · unfold termDurOk
      exact Or.inl ⟨rfl, hdt⟩
  imodintro
  unfold srvV
  iframe
  iframe #

/-- (R2) **The election's term step at the `currentTerm` store** (`electTerm_upd`, its receipt from
`tpRes`). -/
theorem electTerm_R (s : SState) (t0 : Nat) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvVP rc s (some .elect) none ∗ termV rc t0 ⊢
      |NC={E}=> srvV rc { s with term := s.term + 1 } ∗ termV rc (s.term + 1) ∗
        termLb γ i (s.term + 1) ∗ candIs γ i (s.term + 1) s.log.length (lastTerm s.log) ∗
        pubOwn γ i (s.term + 1) 0 ∗ ccfgOwn γ i (s.term + 1) 0 ∗ ccfgOwn γ i (s.term + 1) 0 := by
  iintro ⟨#HI, #Hd, Hv, Ht⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvVP_agree γ rc i X s _ _ $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_termV_agree γ rc i X t0 $$ [Hc Ht]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  have hdt : uint.nat ((X.D.ints.lookup (go!"CurrentTerm" : List w8)).getD (W64 0)) = s.term + 1 := by
    unfold termDurOk at htd
    rcases htd with ⟨h, _⟩ | ⟨t', h, h1, _⟩ | ⟨h, h1⟩
    · cases h
    · cases h
    · exact h1
  iunfold tpRes at Htp
  imod (gprot.electTerm_upd γ _ (crash_hE_gprot hE) i s) $$ [HI Ho Htc Htp]
    with ⟨Ho, Htc, #Hlb, #Hcand, Hpub, Hcc1, Hcc2⟩
  · iframe #; try iframe
  unfold srvVP termV
  imod (ghostVar_update_halves ({ s with term := s.term + 1 }, (none : Option TermPend), (none : Option DiscPend))
    rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imod (ghostVar_update_halves (s.term + 1) rc.dur.tv _ _) $$ Htv Ht with ⟨Htv, Ht⟩
  rw [← durStores_with γ rc i X { s with term := s.term + 1 } none]
  imod Hcl $$ %({ X with s := { s with term := s.term + 1 }, tp := none }) [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Hla] Hs with -
  · iunfold durCore
    dsimp only
    try rw [hdp]
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨hlo, hlc, ?_, ?_, ⟨hci.1, hci.2.1, hci.2.2.1, (by simp), (by simp)⟩⟩
    · unfold voteMatches at hvm ⊢
      obtain ⟨h1, h2⟩ := hvm
      refine ⟨h1, ?_⟩
      rcases h2 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by simp only; omega))
      · exact Or.inr (Or.inr h)
    · unfold termDurOk
      exact Or.inl ⟨rfl, hdt⟩
  imodintro
  unfold srvV
  iframe
  iframe #

/-- (R2) **The commit index at the `commitIndex` store** (inside `cidxCell`'s update,
`E = ⊤ \ ↑cidxN`; `setCidx_upd`). -/
theorem setCidx_R (s : SState) (c c0 : Nat) (hc : c ≤ s.dur.1) :
    Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ cidxV rc c0 ⊢
      |NC={E}=> srvV rc { s with cidx := c } ∗ cidxV rc c := by
  iintro ⟨#HI, #Hd, Hv, Ht⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_cidxV_agree γ rc i X c0 $$ [Hc Ht]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  imod (gprot.setCidx_upd γ _ (crash_hE_gprot hE) i s c hc) $$ [HI Ho Hcc] with ⟨Ho, Hcc⟩
  · iframe #; try iframe
  unfold srvV cidxV
  imod (ghostVar_update_halves ({ s with cidx := c }, (none : Option TermPend), (none : Option DiscPend))
    rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imod (ghostVar_update_halves c rc.dur.cv _ _) $$ Hcv Ht with ⟨Hcv, Ht⟩
  rw [← durStores_with γ rc i X { s with cidx := c } none]
  imod Hcl $$ %({ X with s := { s with cidx := c }, tp := none }) [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp Hla] Hs with -
  · iunfold durCore
    dsimp only
    try rw [hdp]
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    exact ⟨hlo, hlc, hvm, htd, ⟨hci.1, hci.2.1, hci.2.2.1, (by simp), (by simp)⟩⟩
  imodintro
  iframe

/-- (R2) The term atomic's view is the main goroutine's term (was `termCouple_agree`). -/
theorem termV_agree_R (s : SState) (tp : Option TermPend) (dp : Option DiscPend) (t : Nat) :
    srvDurInv γ rc i ∗ srvVP rc s tp dp ∗ termV rc t ⊢
      |NC={E}=> srvVP rc s tp dp ∗ termV rc t ∗ ⌜t = s.term⌝ := by
  iintro ⟨#Hd, Hv, Ht⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_termV_agree γ rc i X t $$ [Hc Ht]
  · iframe
  imod Hcl $$ %X Hc Hs with -
  imodintro
  iframe
  ipureintro
  rw [← Hat, Hag.1]

/-- (R2) The commit index atomic's view is the main goroutine's (was `cidxCouple_agree`). -/
theorem cidxV_agree_R (s : SState) (tp : Option TermPend) (dp : Option DiscPend) (c : Nat) :
    srvDurInv γ rc i ∗ srvVP rc s tp dp ∗ cidxV rc c ⊢
      |NC={E}=> srvVP rc s tp dp ∗ cidxV rc c ∗ ⌜c = s.cidx⌝ := by
  iintro ⟨#Hd, Hv, Ht⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_cidxV_agree γ rc i X c $$ [Hc Ht]
  · iframe
  imod Hcl $$ %X Hc Hs with -
  imodintro
  iframe
  ipureintro
  rw [← Hat, Hag.1]

/-- (R2) The term atomic's value is a lower bound of the server's term (was `termCouple_get_lb`). -/
theorem termV_lb_R (t : Nat) :
    srvDurInv γ rc i ∗ termV rc t ⊢ |NC={E}=> termV rc t ∗ termLb γ i t := by
  iintro ⟨#Hd, Ht⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_termV_agree γ rc i X t $$ [Hc Ht]
  · iframe
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [Hat]
  ihave ⟨Htc, #Hlb⟩ := gprot.termCouple_get_lb γ i t $$ Htc
  imod Hcl $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp Hla] Hs with -
  · iunfold durCore; rw [Hat]; iframe
    ipureintro; exact Hp
  imodintro
  iframe
  all_goals first | (ipureintro; assumption) | iframe #

/-- (R2) A lower bound of the server's term is at most the atomic's value (was `termCouple_lb`). -/
theorem termV_le_R (t t' : Nat) :
    srvDurInv γ rc i ∗ termV rc t ∗ termLb γ i t' ⊢ |NC={E}=> termV rc t ∗ ⌜t' ≤ t⌝ := by
  iintro ⟨#Hd, Ht, #Hlb⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_termV_agree γ rc i X t $$ [Hc Ht]
  · iframe
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [Hat]
  ihave %hle := gprot.termCouple_lb γ i t t' $$ [Htc Hlb]
  · iframe #; try iframe
  imod Hcl $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp Hla] Hs with -
  · iunfold durCore; rw [Hat]; iframe
    ipureintro; exact Hp
  imodintro
  iframe
  all_goals first | (ipureintro; assumption) | iframe #

/-- (R2) A snapshot of the history at the atomic's term (was `termCouple_now`). -/
theorem termV_now_R (t : Nat) (s0 : Snap) :
    Inv γ ∗ srvDurInv γ rc i ∗ isSrv γ i ∗ termV rc t ∗ histLb γ s0 ⊢
      |NC={E}=> termV rc t ∗ ∃ s', histLb γ s' ∗ ⌜snapLe s0 s' ∧ s'.term i = t⌝ := by
  iintro ⟨#HI, #Hd, #Hsrv, Ht, #Hh⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_termV_agree γ rc i X t $$ [Hc Ht]
  · iframe
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [Hat]
  imod (gprot.termCouple_now γ _ (crash_hE_gprot hE) i t s0) $$ [HI Hsrv Htc Hh] with ⟨Htc, HQ⟩
  · iframe #; try iframe
  imod Hcl $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp Hla] Hs with -
  · iunfold durCore; rw [Hat]; iframe
    ipureintro; exact Hp
  imodintro
  iframe
  all_goals first | (ipureintro; assumption) | iframe #

/-- (R2) A leader's replication reads the commit index (was `readCidx_repl`). -/
theorem readCidx_repl_R (T c : Nat) :
    Inv γ ∗ srvDurInv γ rc i ∗ cidxV rc c ∗ leaderIs γ T i ∗ termLb γ i T ⊢
      |NC={E}=> cidxV rc c ∗ (lciOk γ T c ∨ termLb γ i (T + 1)) := by
  iintro ⟨#HI, #Hd, Ht, #Hl, #Hlb⟩ Hnc
  imod (durOpen γ rc i (crash_hE_dur hE)) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  ihave ⟨Hc, Ht, %Hat⟩ := durCore_cidxV_agree γ rc i X c $$ [Hc Ht]
  · iframe
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [Hat]
  imod (gprot.readCidx_repl γ _ (crash_hE_gprot hE) i T c) $$ [HI Hcc Hl Hlb] with ⟨Hcc, HQ⟩
  · iframe #; try iframe
  imod Hcl $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp Hla] Hs with -
  · iunfold durCore; rw [Hat]; iframe
    ipureintro; exact Hp
  imodintro
  iframe
  all_goals first | (ipureintro; assumption) | iframe #

end cells

/-! ## Inside an opened core (for the stores' atomic updates) -/

section core
variable {E : CoPset} (hE : ↑gprotN ⊆ E)
include hE

/-- (R2) A leader's replication reads entry `k` from the log store (inside `logRead_au`, the entry
the store's `logOk` gives; was `readLog_repl` over `logCell`). -/
theorem readLog_repl_core (X : SrvDur) (T k : Nat) (e : Entry) (he : ent X.s.log k = some e) :
    Inv γ ∗ durCore γ rc i X ∗ leaderIs γ T i ∗ termLb γ i T ⊢ |={E}=>
      durCore γ rc i X ∗ (llogIdx γ T k e ∨ termLb γ i (T + 1)) := by
  iintro ⟨#HI, Hc, #Hl, #Hlb⟩
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  imod (gprot.readLog_repl γ _ hE i T k X.s.log e he) $$ [HI Hlc Hl Hlb] with ⟨Hlc, HQ⟩
  · iframe #; try iframe
  imodintro
  iframe HQ
  iunfold durCore
  iframe
  ipureintro; exact Hp

/-- (R2) The stored entries are the protocol log's (from `logOk`). -/
theorem durCore_logOk (X : SrvDur) :
    durCore γ rc i X ⊢ durCore γ rc i X ∗
      ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ uint.nat X.A.ci ≤ X.s.dur.1⌝ := by
  iintro Hc
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  iunfold durCore
  iframe
  ipureintro
  exact ⟨Hp, Hp.1, Hp.2.1, Hp.2.2.2.2.1⟩

/-- (R2) The protocol facts of the core's state (`srvOwn_facts` on it). -/
theorem durCore_facts (X : SrvDur) :
    Inv γ ∗ durCore γ rc i X ⊢ |={E}=> durCore γ rc i X ∗
      ⌜X.s.dur.1 ≤ X.s.log.length ∧ X.s.cidx ≤ X.s.dur.1 ∧ X.s.vterm ≤ X.s.term ∧
        X.s.log.length < 2 ^ 62⌝ := by
  iintro ⟨#HI, Hc⟩
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  imod (gprot.srvOwn_facts γ _ hE i X.s) $$ [HI Ho] with ⟨Ho, -, %hf⟩
  · iframe #; try iframe
  imodintro
  iunfold durCore
  iframe
  ipureintro
  exact ⟨Hp, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.2.1⟩

/-- (R2) The installed snapshot's discard on the opened core (`installDiscard_upd`, R4b/R5's
`DeleteRange` with `Pend.discard`): the new log and durable prefix, the main goroutine's view (lent
in the window) and the pending discard cleared, the store emptied by the delete (`A'.m = ∅`, R5 Q4:
the log after the discard is the committed prefix of length `d.x`, none of which the store keeps),
the store's lower bound `d.x + 1` and the compaction frontier raised to `d.x` (with the main
goroutine's half of its authority; the latest snapshot is at least `d.x`, `latLb`). -/
theorem installDiscard_core (X : SrvDur) (s : SState) (d : DiscPend) (A' : LogAbs) (c0 : Nat)
    (hd : X.s = s ∧ X.dp = some d ∧ X.pend = none)
    (hA : A'.m = ∅ ∧ A'.staged = X.A.staged ∧ A'.ci = X.A.ci) :
    Inv γ ∗ durCore γ rc i X ∗ srvVP rc s X.tp (some d) ∗ monoNatAuthOwn rc.dur.comp (1 : Qp).half c0 ∗
      latLb rc d.x ∗ applLb rc d.x ⊢ |={E}=>
      ∃ (X' : SrvDur), durCore γ rc i X' ∗ srvVP rc X'.s X.tp none ∗
        monoNatAuthOwn rc.dur.comp (1 : Qp).half d.x ∗ durLb γ i d.x ∗
        ([∗list] k ↦ e ∈ X'.s.log, CIdx γ (k + 1) e) ∗
        ⌜X'.A = A' ∧ X'.D = X.D ∧ X'.lat = X.lat ∧ X'.pend = X.pend ∧ X'.dp = none ∧ X'.c = d.x ∧
          X'.lo = d.x + 1 ∧ X'.s.log.length = d.x ∧ lastTerm X'.s.log = d.st ∧ X'.s.dur.1 = d.x ∧
          X'.s.term = s.term ∧ X'.s.vterm = s.vterm ∧ X'.s.vcand = s.vcand ∧ X'.s.cidx = s.cidx⌝ := by
  iintro ⟨#HI, Hc, Hv, Hcm, #Hll, #Happ⟩
  obtain ⟨hs, hdp, hpe⟩ := hd
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla, Hbp⟩
  rw [hs, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci, ⟨⟨hdl, hpd, hll⟩, hcd, hq5a, hq5b⟩⟩ := Hp
  have hcx := hcd d rfl
  iunfold dpRes at Hdp
  icases Hdp with ⟨#Hae, #Hl, %hpre⟩
  imod (gprot.srvOwn_durLb γ _ hE i s) $$ [HI Ho] with ⟨Ho, #Hdl0⟩
  · iframe #; try iframe
  imod (gprot.installDiscard_upd γ _ hE i s d.x d.st d.ℓ hpre.1 hpre.2.1 hpre.2.2) $$ [HI Ho Hlc Hdv Hae Hl]
    with ⟨%L', %dd, Ho, Hlc, Hdv, #Hlbx, %hL, HC⟩
  · iframe #; try iframe
  ihave %hmono := gprot.durView_lb γ i _ dd.1 s.dur.1 $$ [Hdv Hdl0]
  · iframe #; try iframe
  unfold latLb
  ihave %hlat := monoNatLbOwn_valid rc.dur.lat 1 _ d.x $$ Hla Hll
  imod (gprot.monoNat_update_halves rc.dur.comp X.c c0 d.x (by omega)) $$ [Hcomp Hcm] with ⟨Hcomp, Hcm, -⟩
  · iframe
  unfold srvVP
  imod (ghostVar_update_halves ({ s with log := L', dur := dd }, X.tp, (none : Option DiscPend)) rc.dur.sv _ _)
    $$ Hsv Hv with ⟨Hsv, Hv⟩
  ihave Hbp' : bootPinF rc X.lat X.pend none $$ [Hbp]
  · unfold bootPinF
    icases Hbp with (Hb | -)
    · ileft; iexact Hb
    · iright
      obtain ⟨m, b, hlm, hmi, -⟩ := hq5b d rfl
      rw [hlm]
      unfold latApplF
      iright
      rw [hmi]
      iexact Happ
  imodintro
  iexists ({ X with s := { s with log := L', dur := dd }, A := A', lo := d.x + 1, c := d.x, dp := none })
  isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hla Hbp']
  · iunfold durCore
    dsimp only
    rw [hA.2.1]
    simp only [dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨?_, by omega, hvm, htd, by rw [hA.2.2]; exact Nat.le_trans hci hmono, ⟨⟨fun d' h => (by cases h), ?_, by have := hlat.2; omega⟩, fun d' h => (by cases h), (by simp), (by simp)⟩⟩
    · unfold logOk
      rw [hA.1]
      constructor
      · intro k e h; simp at h
      · intro k h1 h2; omega
    · intro x st id h; rw [hpe] at h; cases h
  iframe
  iframe #
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hL.1, hL.2.1, hL.2.2, rfl, rfl, rfl, rfl⟩

end core

/-! ## Generic atomic updates of the stores

Each builds the store's (crash-token) atomic update from `srvDurInv`: it opens the invariant (its
core without a later), hands the store's authority over, and at the commit (`f`'s new state) runs
the caller's step on the core, which must re-establish it with the other stores unchanged. -/

section stores

theorem crash_dur_storeN : (↑durN : CoPset) ⊆ ⊤ \ ↑storeN := by
  unfold durN raftN storeN; solve_ndisj

/-- (R2) A log-store write (`StoreLogs`, `StoreLog`, `StageCommitIndex`: `f` the write's effect). -/
theorem logWrite_au (f : LogAbs → LogAbs) (R Ψ : IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> ∃ X' : SrvDur, durCore γ rc i X' ∗
        ⌜X'.A = f X.A ∧ X'.D = X.D ∧ X'.lat = X.lat ∧ X'.pend = X.pend ∧ X'.dp = X.dp⌝ ∗ |={⊤ \ ↑storeN}=> Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs, rc.ownL A ∗ (rc.ownL (f A) ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  iintro #Hd HR Hf Hnc
  imod (durOpen γ rc i crash_dur_storeN) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hlat⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.A
  iframe HL
  iintro HL
  imod Hmask
  imod Hf $$ %X Hc HR with ⟨%X', Hc', %hX', HΨ⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hX'
  imod Hcl $$ %X' Hc' [HL HS HSS Hlat] with -
  · iunfold durStores; rw [h1, h2, h3, h4, h5]; inext; iframe
  iexact HΨ

/-- (R2) A log-store `DeleteRange(mn, mx)` (the store chooses the new `hi'`). -/
theorem logDelete_au (mn mx : Nat) (R Ψ : IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ (X : SrvDur) (hi' : w64), durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> ∃ X' : SrvDur,
        durCore γ rc i X' ∗
        ⌜X'.A = X.A.delete mn mx hi' ∧ X'.D = X.D ∧ X'.lat = X.lat ∧ X'.pend = X.pend ∧ X'.dp = X.dp⌝ ∗ |={⊤ \ ↑storeN}=> Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs, rc.ownL A ∗
        (∀ hi' : w64, rc.ownL (A.delete mn mx hi') ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  iintro #Hd HR Hf Hnc
  imod (durOpen γ rc i crash_dur_storeN) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hlat⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.A
  iframe HL
  iintro %hi' HL
  imod Hmask
  imod Hf $$ %X %hi' Hc HR with ⟨%X', Hc', %hX', HΨ⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hX'
  imod Hcl $$ %X' Hc' [HL HS HSS Hlat] with -
  · iunfold durStores; rw [h1, h2, h3, h4, h5]; inext; iframe
  iexact HΨ

/-- (R2) A log-store read (`GetLog`, `LastIndex`, `GetCommitIndex`): the caller's result over the
opened core (the store's state `X.A`, its coupling with `X.s`). -/
theorem logRead_au (R : IProp GF) (Ψ : LogAbs → IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> durCore γ rc i X ∗ |={⊤ \ ↑storeN}=> Ψ X.A) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs, rc.ownL A ∗ (rc.ownL A ={∅, ⊤ \ ↑storeN}=∗ Ψ A) := by
  iintro #Hd HR Hf Hnc
  imod (durOpen γ rc i crash_dur_storeN) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  imod Hf $$ %X Hc HR with ⟨Hc, HΨ⟩
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hlat⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.A
  iframe HL
  iintro HL
  imod Hmask
  imod Hcl $$ %X Hc [HL HS HSS Hlat] with -
  · iunfold durStores; inext; iframe
  iexact HΨ

/-- (R2) A stable-store write (`f` the write's effect). -/
theorem stableWrite_au (f : StableAbs → StableAbs) (R Ψ : IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> ∃ X' : SrvDur, durCore γ rc i X' ∗
        ⌜X'.D = f X.D ∧ X'.A = X.A ∧ X'.lat = X.lat ∧ X'.pend = X.pend ∧ X'.dp = X.dp⌝ ∗ |={⊤ \ ↑storeN}=> Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D : StableAbs, rc.ownS D ∗ (rc.ownS (f D) ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  iintro #Hd HR Hf Hnc
  imod (durOpen γ rc i crash_dur_storeN) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hlat⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.D
  iframe HS
  iintro HS
  imod Hmask
  imod Hf $$ %X Hc HR with ⟨%X', Hc', %hX', HΨ⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hX'
  imod Hcl $$ %X' Hc' [HL HS HSS Hlat] with -
  · iunfold durStores; rw [h1, h2, h3, h4, h5]; inext; iframe
  iexact HΨ

/-- (R2) A stable-store read. -/
theorem stableRead_au (R : IProp GF) (Ψ : StableAbs → IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> durCore γ rc i X ∗ |={⊤ \ ↑storeN}=> Ψ X.D) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D : StableAbs, rc.ownS D ∗ (rc.ownS D ={∅, ⊤ \ ↑storeN}=∗ Ψ D) := by
  iintro #Hd HR Hf Hnc
  imod (durOpen γ rc i crash_dur_storeN) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  imod Hf $$ %X Hc HR with ⟨Hc, HΨ⟩
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hlat⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.D
  iframe HS
  iintro HS
  imod Hmask
  imod Hcl $$ %X Hc [HL HS HSS Hlat] with -
  · iunfold durStores; inext; iframe
  iexact HΨ

/-- (R2) A snapshot-store commit (a sink's `Close`: `f` the store's new latest); the caller's step
also gets `latestDur` (under its later: it mentions `snapP`) and re-establishes it. -/
theorem snapWrite_au (f : SnapLatest → SnapLatest) (R Ψ : IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ ▷ latestDur γ rc i X.lat X.pend X.dp -∗ R -∗
        |={(⊤ \ ↑storeN) \ ↑durN}=> ∃ X' : SrvDur, durCore γ rc i X' ∗ ▷ latestDur γ rc i X'.lat X'.pend X'.dp ∗
          ⌜X'.lat = f X.lat ∧ X'.A = X.A ∧ X'.D = X.D ∧ X'.dp = X.dp⌝ ∗ |={⊤ \ ↑storeN}=> Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old : SnapLatest, rc.ownSS old ∗ (rc.ownSS (f old) ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  iintro #Hd HR Hf Hnc
  imod (durOpen γ rc i crash_dur_storeN) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hlat⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.lat
  iframe HSS
  iintro HSS
  imod Hmask
  imod Hf $$ %X Hc [Hlat] HR with ⟨%X', Hc', Hlat, %hX', HΨ⟩
  · inext; iexact Hlat
  obtain ⟨h1, h2, h3, h4⟩ := hX'
  imod Hcl $$ %X' Hc' [HL HS HSS Hlat] with -
  · iunfold durStores; rw [h1, h2, h3, h4]; inext; iframe
  iexact HΨ

/-- (R2) A snapshot-store read (`List`, `Open`). -/
theorem snapRead_au (R : IProp GF) (Ψ : SnapLatest → IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ ▷ latestDur γ rc i X.lat X.pend X.dp -∗ R -∗
        |={(⊤ \ ↑storeN) \ ↑durN}=> durCore γ rc i X ∗ ▷ latestDur γ rc i X.lat X.pend X.dp ∗ |={⊤ \ ↑storeN}=> Ψ X.lat) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old : SnapLatest, rc.ownSS old ∗ (rc.ownSS old ={∅, ⊤ \ ↑storeN}=∗ Ψ old) := by
  iintro #Hd HR Hf Hnc
  imod (durOpen γ rc i crash_dur_storeN) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hlat⟩
  imod Hf $$ %X Hc Hlat HR with ⟨Hc, Hlat, HΨ⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.lat
  iframe HSS
  iintro HSS
  imod Hmask
  imod Hcl $$ %X Hc [HL HS HSS Hlat] with -
  · iunfold durStores; inext; iframe
  iexact HΨ

/-- (R2) `StageCommitIndex(idx)` by the main goroutine (its view of the staged index updated; no
window: volatile). -/
theorem stageCommit_au (D : StableAbs) (g idx : w64) (Ψ : IProp GF) :
    srvDurInv γ rc i -∗ stVS rc D g -∗ (stVS rc D idx ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs, rc.ownL A ∗ (rc.ownL { A with staged := idx } ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  iintro #Hd Hst Hk
  iapply (logWrite_au γ rc i (fun A => { A with staged := idx })
    iprop(stVS rc D g ∗ (stVS rc D idx ={⊤ \ ↑storeN}=∗ Ψ)) Ψ) $$ Hd [Hst Hk]
  · iframe
  iintro %X Hc ⟨Hst, Hk⟩
  ihave ⟨Hc, Hst, %Hag⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hD, hg⟩ := Hag
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  unfold stVS
  imod (ghostVar_update_halves (X.D, idx) rc.dur.st _ _) $$ Hst0 Hst with ⟨Hst0, Hst⟩
  imodintro
  iexists { X with A := { X.A with staged := idx } }
  isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
  · iunfold durCore
    iframe
    ipureintro
    exact Hp
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [hD]
  iapply Hk $$ Hst

end stores

/-! ### Windows: making and taking back `winRes` -/

theorem crash_gprot_store : (↑gprotN : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN := by
  unfold gprotN storeN durN raftN; solve_ndisj

theorem LogAbs.store_staged (A : LogAbs) (first : Nat) (es : RLog) :
    (A.store first es).staged = A.staged := rfl
theorem LogAbs.store_ci (A : LogAbs) (first : Nat) (es : RLog) :
    (A.store first es).ci = A.staged := rfl
theorem LogAbs.store_m (A : LogAbs) (first : Nat) (es : RLog) :
    (A.store first es).m = LogAbs.ins A.m first es := rfl
theorem LogAbs.delete_staged (A : LogAbs) (mn mx : Nat) (hi : w64) :
    (A.delete mn mx hi).staged = A.staged := rfl
theorem LogAbs.delete_ci (A : LogAbs) (mn mx : Nat) (hi : w64) :
    (A.delete mn mx hi).ci = A.ci := rfl
theorem LogAbs.delete_m (A : LogAbs) (mn mx : Nat) (hi : w64) :
    (A.delete mn mx hi).m = LogAbs.del A.m mn mx := rfl

/-- `LogAbs.ins` pointwise (as `InmemStore__StoreLogs`'s, which a defs module cannot import). -/
theorem crash_lookup_ins (m : GMap Nat Entry) (first : Nat) (es : RLog) (k : Nat) :
    (LogAbs.ins m first es).lookup k =
      if first ≤ k ∧ k < first + es.length then es[k - first]? else m.lookup k := by
  induction es generalizing m first with
  | nil => simp only [LogAbs.ins, List.length_nil]; rw [if_neg (by omega)]
  | cons e es ih =>
    simp only [LogAbs.ins]
    rw [ih]
    show _ = _
    by_cases h1 : first + 1 ≤ k ∧ k < first + 1 + es.length
    · rw [if_pos h1, if_pos (by simp; omega)]
      rw [show k - first = (k - (first + 1)) + 1 by omega, List.getElem?_cons_succ]
    · rw [if_neg h1]
      by_cases h2 : first = k
      · subst h2
        rw [if_pos (by simp), Nat.sub_self, List.getElem?_cons_zero]
        exact (GMap.lookup_insert m first e)
      · rw [GMap.lookup_insert_ne m e h2, if_neg (by simp; omega)]

/-- (R2) Appending `es` at the log's end keeps the store's coupling. -/
theorem logOk_store (A : LogAbs) (L es : RLog) (lo : Nat) (h : logOk A L lo) :
    logOk (A.store (L.length + 1) es) (L ++ es) lo := by
  obtain ⟨h1, h2⟩ := h
  unfold logOk
  rw [LogAbs.store_m]
  constructor
  · intro k e hk
    rw [crash_lookup_ins] at hk
    split at hk
    · rename_i hr
      have hk' : k = L.length + 1 + (k - (L.length + 1)) := by omega
      rw [hk', gprot.ent_append_right]; exact hk
    · exact gprot.ent_prefix (List.prefix_append L es) (h1 k e hk)
  · intro k hlo hk
    rw [crash_lookup_ins]
    split
    · rename_i hr
      have hk' : k = L.length + 1 + (k - (L.length + 1)) := by omega
      conv => rhs; rw [hk']
      rw [gprot.ent_append_right]
    · rename_i hr
      simp only [List.length_append] at hk
      rw [gprot.ent_append_left L es k (by omega)]
      exact h2 k hlo (by omega)

/-- (R2) The follower's append matches the request (as `handlers/Base`'s `matched_store`, which a core
module cannot import). -/
theorem crash_matched_store (L : RLog) (prev pt : Nat) (ents : RLog) (j : Nat)
    (hp : prevMatch L prev pt) (hm : matchedUpTo L prev ents j) (hl : L.length = prev + j)
    (hj : j ≤ ents.length) :
    prevMatch (L ++ ents.drop j) prev pt ∧ matchedUpTo (L ++ ents.drop j) prev ents ents.length := by
  refine ⟨?_, ⟨Nat.le_refl _, fun j' hj' => ?_⟩⟩
  · rcases hp with hp | ⟨h1, h2⟩
    · left; exact hp
    · right; refine ⟨by simp; omega, ?_⟩; rw [termAt_append_left _ _ _ h1]; exact h2
  · by_cases hjj : j' < j
    · obtain ⟨h1, h2⟩ := hm.2 j' hjj
      refine ⟨by simp; omega, ?_⟩
      rw [termAt_append_left _ _ _ h1]; exact h2
    · refine ⟨by simp; omega, ?_⟩
      rw [termAt_append_right _ _ _ (by omega), termAt_drop _ _ _ (by omega)]
      congr 1; omega

/-- `LogAbs.del` pointwise. -/
theorem crash_lookup_del (m : GMap Nat Entry) (mn mx k : Nat) :
    (LogAbs.del m mn mx).lookup k = if mn ≤ k ∧ k ≤ mx then none else m.lookup k := by
  unfold LogAbs.del
  show (GMap.filter _ m) !! k = _
  rw [GMap.lookup_filter]
  by_cases hr : mn ≤ k ∧ k ≤ mx
  · rw [if_pos hr]; cases m !! k <;> simp [Option.filter, hr]
  · rw [if_neg hr]; cases hc : m !! k <;> simp [Option.filter, hr]

/-- (R2) Deleting the log's tail from `n + 1` keeps the store's coupling with the log's prefix. -/
theorem logOk_delete (A : LogAbs) (L : RLog) (lo n mx : Nat) (hi : w64) (h : logOk A L lo)
    (hmx : L.length ≤ mx) : logOk (A.delete (n + 1) mx hi) (L.take n) lo := by
  obtain ⟨h1, h2⟩ := h
  unfold logOk
  rw [LogAbs.delete_m]
  constructor
  · intro k e hk
    rw [crash_lookup_del] at hk
    split at hk
    · cases hk
    · rename_i hr
      have he := h1 k e hk
      have hkL := gprot.ent_le_length he
      rw [ent_take _ _ _ (by omega)]; exact he
  · intro k hlo hk
    rw [crash_lookup_del]
    have hkn : k ≤ n := by simp at hk; omega
    rw [if_neg (by omega), ent_take _ _ _ hkn]
    exact h2 k hlo (by simp at hk; omega)

/-- (R2) **A store of `es` at `first` keeps the coupling** with the log `L ++ X` when the stored entries
are the new log's and every index of the new log outside them is one of `L`'s. -/
theorem logOk_store_gen (A : LogAbs) (L X : RLog) (lo first : Nat) (es : RLog) (h : logOk A L lo)
    (hin : ∀ t, t < es.length → ent (L ++ X) (first + t) = es[t]?)
    (hout : ∀ x, lo ≤ x → x ≤ (L ++ X).length → ¬ (first ≤ x ∧ x < first + es.length) → x ≤ L.length) :
    logOk (A.store first es) (L ++ X) lo := by
  obtain ⟨h1, h2⟩ := h
  unfold logOk
  rw [LogAbs.store_m]
  constructor
  · intro k e hk
    rw [crash_lookup_ins] at hk
    split at hk
    · rename_i hr
      have := hin (k - first) (by omega)
      rw [show first + (k - first) = k by omega] at this
      rw [this]; exact hk
    · exact gprot.ent_prefix (List.prefix_append L X) (h1 k e hk)
  · intro k hlo hk
    rw [crash_lookup_ins]
    split
    · rename_i hr
      have := hin (k - first) (by omega)
      rw [show first + (k - first) = k by omega] at this
      rw [this]
    · rename_i hr
      have hkL := hout k hlo hk hr
      rw [gprot.ent_append_left L X k hkL]
      exact h2 k hlo hkL

/-- (R2) The follower's (re-)store of `ents.drop k` at `prev + k + 1` with the log becoming
`L ++ ents.drop j` (`k ≤ j`, the entries `k..j-1` already the log's). -/
theorem logOk_fstore (A : LogAbs) (L ents : RLog) (lo prev j k : Nat) (h : logOk A L lo)
    (hkj : k ≤ j) (hov : ∀ m, k ≤ m → m < j → ent L (prev + m + 1) = ents[m]?)
    (hl : (j < ents.length ∧ L.length = prev + j) ∨ (j = ents.length ∧ prev + j ≤ L.length)) :
    logOk (A.store (prev + k + 1) (ents.drop k)) (L ++ ents.drop j) lo := by
  apply logOk_store_gen A L (ents.drop j) lo (prev + k + 1) (ents.drop k) h
  · intro t ht
    simp only [List.length_drop] at ht
    rw [List.getElem?_drop]
    by_cases hm : k + t < j
    · rw [gprot.ent_append_left L _ _ (by omega), show prev + k + 1 + t = prev + (k + t) + 1 by omega]
      exact hov (k + t) (by omega) hm
    · rcases hl with ⟨hj, hlen⟩ | ⟨hj, hlen⟩
      · rw [show prev + k + 1 + t = L.length + 1 + (k + t - j) by omega, gprot.ent_append_right,
          List.getElem?_drop]
        congr 1; omega
      · omega
  · intro x hlo hx hr
    simp only [List.length_append, List.length_drop] at hx hr
    rcases hl with ⟨hj, hlen⟩ | ⟨hj, hlen⟩ <;> omega

/-- (R2) **Lending a window**: the pending-write record set to `p` (half lent), a quarter of each
view lent. -/
theorem winRes_make (s : SState) (p : Pend) (D : StableAbs) (g : w64)
    (h : pendPre γ i s p ∧ winPure s D g p) (hp0 : pendDp p = none) :
    ghostVar rc.dur.pw 1 (none : Option Pend) ∗ srvV rc s ∗ stVS rc D g ∗ pendHyps γ i s p ⊢
      |==> (winRes γ rc i s p ∗ ghostVar rc.dur.pw (1 : Qp).half (some p) ∗ srvVq rc s ∗
        stVq rc D g) := by
  iintro ⟨Hpw, Hv, Hst, Hh⟩
  ihave Hpw := ghostVar_update (some p) rc.dur.pw (none : Option Pend) $$ Hpw
  imod Hpw
  ihave ⟨Hpw1, Hpw2⟩ := (ghostVar_split_half rc.dur.pw 1 (some p)).1 $$ Hpw
  unfold srvV stVS
  ihave ⟨Hv1, Hv2⟩ := (ghostVar_split_half rc.dur.sv (1 : Qp).half _).1 $$ Hv
  ihave ⟨Hs1, Hs2⟩ := (ghostVar_split_half rc.dur.st (1 : Qp).half _).1 $$ Hst
  imodintro
  unfold winRes srvVq srvVPq stVq
  rw [hp0]
  iframe Hpw2 Hv2 Hs2
  iframe
  ipureintro; exact ⟨h.2, h.1⟩

/-- (R2) **A window given back**: its state and step are the lender's (the kept halves agree), and
the lender's views and record are whole again. -/
theorem winRes_back (s s' : SState) (p p' : Pend) (D : StableAbs) (g : w64) (hp0 : pendDp p = none) :
    winRes γ rc i s' p' ∗ ghostVar rc.dur.pw (1 : Qp).half (some p) ∗ srvVq rc s ∗ stVq rc D g ⊢
      ⌜s' = s ∧ p' = p⌝ ∗ ghostVar rc.dur.pw 1 (some p) ∗ srvV rc s ∗ stVS rc D g ∗
        pendHyps γ i s p ∗ ⌜pendPre γ i s p ∧ winPure s D g p⌝ := by
  iintro ⟨HW, Hpw, Hq, Hsq⟩
  unfold winRes srvVq srvVPq stVq
  icases HW with ⟨Hpw', Hq', ⟨%D', %g', Hs', %hw⟩, Hh, %hp⟩
  icombine Hpw' Hpw gives %h1
  icombine Hq' Hq gives %h2
  icombine Hs' Hsq gives %h3
  have e1 := h1.2
  have e2 := h2.2
  have e3 := h3.2
  simp only [Option.some.injEq, Prod.mk.injEq] at e1 e2 e3
  obtain ⟨rfl, -, -⟩ := e2
  subst e1
  obtain ⟨rfl, rfl⟩ := e3
  rw [hp0]
  ihave Hpw := (ghostVar_split_half rc.dur.pw 1 (some p')).2 $$ [Hpw' Hpw]
  · iframe
  unfold srvV stVS
  ihave Hv := (ghostVar_split_half rc.dur.sv (1 : Qp).half _).2 $$ [Hq' Hq]
  · iframe
  ihave Hst := (ghostVar_split_half rc.dur.st (1 : Qp).half _).2 $$ [Hs' Hsq]
  · iframe
  iframe
  ipureintro
  exact ⟨⟨rfl, rfl⟩, hp, hw⟩

/-- (R2) `winRes_make` from a pending-phase view (the install's discard: `srvVP s none (some d)`). -/
theorem winRes_makeP (s : SState) (p : Pend) (D : StableAbs) (g : w64)
    (h : pendPre γ i s p ∧ winPure s D g p) :
    ghostVar rc.dur.pw 1 (none : Option Pend) ∗ srvVP rc s none (pendDp p) ∗ stVS rc D g ∗ pendHyps γ i s p ⊢
      |==> (winRes γ rc i s p ∗ ghostVar rc.dur.pw (1 : Qp).half (some p) ∗ srvVPq rc s none (pendDp p) ∗
        stVq rc D g) := by
  iintro ⟨Hpw, Hv, Hst, Hh⟩
  ihave Hpw := ghostVar_update (some p) rc.dur.pw (none : Option Pend) $$ Hpw
  imod Hpw
  ihave ⟨Hpw1, Hpw2⟩ := (ghostVar_split_half rc.dur.pw 1 (some p)).1 $$ Hpw
  unfold srvVP stVS
  ihave ⟨Hv1, Hv2⟩ := (ghostVar_split_half rc.dur.sv (1 : Qp).half _).1 $$ Hv
  ihave ⟨Hs1, Hs2⟩ := (ghostVar_split_half rc.dur.st (1 : Qp).half _).1 $$ Hst
  imodintro
  unfold winRes srvVPq stVq
  iframe Hpw2 Hv2 Hs2
  iframe
  ipureintro; exact ⟨h.2, h.1⟩

theorem winRes_backP (s s' : SState) (p p' : Pend) (D : StableAbs) (g : w64) :
    winRes γ rc i s' p' ∗ ghostVar rc.dur.pw (1 : Qp).half (some p) ∗ srvVPq rc s none (pendDp p) ∗
      stVq rc D g ⊢
      ⌜s' = s ∧ p' = p⌝ ∗ ghostVar rc.dur.pw 1 (some p) ∗ srvVP rc s none (pendDp p) ∗ stVS rc D g ∗
        pendHyps γ i s p ∗ ⌜pendPre γ i s p ∧ winPure s D g p⌝ := by
  iintro ⟨HW, Hpw, Hq, Hsq⟩
  unfold winRes srvVPq stVq
  icases HW with ⟨Hpw', Hq', ⟨%D', %g', Hs', %hw⟩, Hh, %hp⟩
  icombine Hpw' Hpw gives %h1
  icombine Hs' Hsq gives %h3
  have e1 := h1.2
  have e3 := h3.2
  simp only [Option.some.injEq, Prod.mk.injEq] at e1 e3
  subst e1
  obtain ⟨rfl, rfl⟩ := e3
  icombine Hq' Hq gives %h2
  have e2 := h2.2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, -, -⟩ := e2
  ihave Hpw := (ghostVar_split_half rc.dur.pw 1 (some p')).2 $$ [Hpw' Hpw]
  · iframe
  unfold srvVP stVS
  ihave Hv := (ghostVar_split_half rc.dur.sv (1 : Qp).half _).2 $$ [Hq' Hq]
  · iframe
  ihave Hst := (ghostVar_split_half rc.dur.st (1 : Qp).half _).2 $$ [Hs' Hsq]
  · iframe
  iframe
  ipureintro
  exact ⟨⟨rfl, rfl⟩, hp, hw⟩

/-! ## The durable writes that fire a step (R1 §2.2)

Each gives both arguments of the store's write contract: the window (`logWin`/`stWin` of the write,
made of a quarter of the caller's views and the law's premises: `winRes`) and the atomic update,
which keeps the views' other quarters and, at the commit, fires the step and hands the stepped
views to the caller's continuation. -/

section commits

/-- (R2) **The leader's appends** (no-ops, barriers, commands) at `StoreLogs`' commit
(`leaderAppendCmd_upd`), at `first = |s.log| + 1`, the staged index durable. -/
theorem storeLogs_app_win (s : SState) (es : RLog) (D : StableAbs) (g : w64)
    (hpre : pendPre γ i s (.app es)) (hg : uint.nat g ≤ s.dur.1) (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc s -∗ stVS rc D g -∗ pendHyps γ i s (.app es) -∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s with log := s.log ++ es } -∗ stVS rc D g -∗
        ([∗list] k ↦ e ∈ es, llogIdx γ s.term (s.log.length + 1 + k) e) ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |==> (logWin γ rc i (.store (s.log.length + 1) es) ∗
      (logWin γ rc i (.store (s.log.length + 1) es) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (rc.ownL (A.store (s.log.length + 1) es) ={∅, ⊤ \ ↑storeN}=∗ Ψ))) := by
  iintro #HI #Hd Hpw Hv Hst Hh Hk
  imod (winRes_make γ rc i s (.app es) D g ⟨hpre, hg⟩ rfl) $$ [Hpw Hv Hst Hh] with ⟨HW, Hpw, Hq, Hsq⟩
  · iframe
  imodintro
  isplitl [HW]
  · iunfold logWin; ileft; iexists s, (Pend.app es); iframe HW; ipureintro; rfl
  iintro HW
  iunfold logWin at HW
  icases HW with (⟨%s', %p', %hok, HW⟩ | ⟨%mn, %mx, %hop, -⟩)
  rotate_left
  · cases hop
  ihave ⟨%heq, Hpw, Hv, Hst, Hh, -⟩ := winRes_back γ rc i s s' (.app es) p' D g rfl $$ [HW Hpw Hq Hsq]
  · iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hpw := ghostVar_update (none : Option Pend) rc.dur.pw (some (Pend.app es)) $$ Hpw
  iapply (logWrite_au γ rc i (fun A => A.store (s'.log.length + 1) es)
    iprop(srvV rc s' ∗ stVS rc D g ∗ pendHyps γ i s' (.app es) ∗ (|==> ghostVar rc.dur.pw 1 (none : Option Pend)) ∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s' with log := s'.log ++ es } -∗ stVS rc D g -∗
        ([∗list] k ↦ e ∈ es, llogIdx γ s'.term (s'.log.length + 1 + k) e) ={⊤ \ ↑storeN}=∗ Ψ)) Ψ) $$ Hd [Hv Hst Hh Hpw Hk]
  · iframe
  iintro %X Hc ⟨Hv, Hst, Hh, Hpw, Hk⟩
  imod Hpw
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s' $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  obtain ⟨hD, hstg⟩ := Hag2
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  iunfold pendHyps at Hh
  icases Hh with ⟨#Hl, Hr, Hops⟩
  imod (gprot.leaderAppendCmd_upd γ _ crash_gprot_store i s' es hpre) $$ [HI Ho Hlc Hl Hr Hops]
    with ⟨Ho, Hlc, #Hidx⟩
  · iframe #; try iframe
  unfold srvV
  imod (ghostVar_update_halves ({ s' with log := s'.log ++ es }, (none : Option TermPend), (none : Option DiscPend))
    rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imodintro
  iexists ({ X with s := { s' with log := s'.log ++ es }, A := X.A.store (s'.log.length + 1) es, tp := none })
  isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
  · iunfold durCore
    dsimp only
    try rw [hdp]
    rw [LogAbs.store_staged, LogAbs.store_ci]
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨logOk_store _ _ _ _ hlo, hlc, hvm, htd, ?_⟩
    exact ⟨by rw [hstg]; exact hg, q2_step _ _ _ _ _ _ _ _ (Nat.le_refl _) (fun x st _ h => prevMatch_append _ _ _ _ h) hci.2.1, hci.2.2.1, (by simp), (by simp)⟩
  isplitl []
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, by first | rfl | exact hdp⟩
  ihave HΨ := Hk $$ Hpw Hv Hst Hidx
  iexact HΨ

/-- (R2) **The leader's configuration entry** at `StoreLogs`' commit (`leaderAppendCfg_upd`). -/
theorem storeLogs_cfg_win (s : SState) (e : Entry) (k p : Nat) (D : StableAbs) (g : w64)
    (hpre : pendPre γ i s (.cfg e k p)) (hg : uint.nat g ≤ s.dur.1) (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc s -∗ stVS rc D g -∗ pendHyps γ i s (.cfg e k p) -∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s with log := s.log ++ [e] } -∗ stVS rc D g -∗
        ccfgOwn γ i s.term (lastCfgIdx s.log) -∗
        llogIdx γ s.term (s.log.length + 1) e ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |==> (logWin γ rc i (.store (s.log.length + 1) [e]) ∗
      (logWin γ rc i (.store (s.log.length + 1) [e]) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (rc.ownL (A.store (s.log.length + 1) [e]) ={∅, ⊤ \ ↑storeN}=∗ Ψ))) := by
  iintro #HI #Hd Hpw Hv Hst Hh Hk
  imod (winRes_make γ rc i s (.cfg e k p) D g ⟨hpre, hg⟩ rfl) $$ [Hpw Hv Hst Hh] with ⟨HW, Hpw, Hq, Hsq⟩
  · iframe
  imodintro
  isplitl [HW]
  · iunfold logWin; ileft; iexists s, (Pend.cfg e k p); iframe HW; ipureintro; rfl
  iintro HW
  iunfold logWin at HW
  icases HW with (⟨%s', %p', %hok, HW⟩ | ⟨%mn, %mx, %hop, -⟩)
  rotate_left
  · cases hop
  ihave ⟨%heq, Hpw, Hv, Hst, Hh, -⟩ := winRes_back γ rc i s s' (.cfg e k p) p' D g rfl $$ [HW Hpw Hq Hsq]
  · iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hpw := ghostVar_update (none : Option Pend) rc.dur.pw (some (Pend.cfg e k p)) $$ Hpw
  iapply (logWrite_au γ rc i (fun A => A.store (s'.log.length + 1) [e])
    iprop(srvV rc s' ∗ stVS rc D g ∗ pendHyps γ i s' (.cfg e k p) ∗ (|==> ghostVar rc.dur.pw 1 (none : Option Pend)) ∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s' with log := s'.log ++ [e] } -∗ stVS rc D g -∗
        ccfgOwn γ i s'.term (lastCfgIdx s'.log) -∗
        llogIdx γ s'.term (s'.log.length + 1) e ={⊤ \ ↑storeN}=∗ Ψ)) Ψ) $$ Hd [Hv Hst Hh Hpw Hk]
  · iframe
  iintro %X Hc ⟨Hv, Hst, Hh, Hpw, Hk⟩
  imod Hpw
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s' $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  obtain ⟨hD, hstg⟩ := Hag2
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  iunfold pendHyps at Hh
  icases Hh with ⟨#Hl, Hcf, #Hci, Hr⟩
  imod (gprot.leaderAppendCfg_upd γ _ crash_gprot_store i s' e k p hpre) $$ [HI Ho Hlc Hl Hcf Hci Hr]
    with ⟨Ho, Hlc, Hcf, #Hidx⟩
  · iframe #; try iframe
  unfold srvV
  imod (ghostVar_update_halves ({ s' with log := s'.log ++ [e] }, (none : Option TermPend), (none : Option DiscPend))
    rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imodintro
  iexists ({ X with s := { s' with log := s'.log ++ [e] }, A := X.A.store (s'.log.length + 1) [e], tp := none })
  isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
  · iunfold durCore
    dsimp only
    try rw [hdp]
    rw [LogAbs.store_staged, LogAbs.store_ci]
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨logOk_store _ _ _ _ hlo, hlc, hvm, htd, ?_⟩
    exact ⟨by rw [hstg]; exact hg, q2_step _ _ _ _ _ _ _ _ (Nat.le_refl _) (fun x st _ h => prevMatch_append _ _ _ _ h) hci.2.1, hci.2.2.1, (by simp), (by simp)⟩
  isplitl []
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, by first | rfl | exact hdp⟩
  ihave HΨ := Hk $$ Hpw Hv Hst Hcf Hidx
  iexact HΨ

/-- (R2) **The follower's append** at `StoreLogs`' commit (`followerStore_upd`), then, with
`lc = some v`, the commit learnt with it (`learnCommitFollower` of `min lci v`, so that the written
staged index `g ≤ min lci v` is durable). -/
theorem storeLogs_fstore_win_k (s : SState) (prev pt : Nat) (ents : RLog) (lci j k : Nat)
    (lc : Option Nat) (D : StableAbs) (g : w64)
    (hpre : pendPre γ i s (.fstore prev pt ents lci j lc))
    (hk : k ≤ j ∧ ∀ m, k ≤ m → m < j → ent s.log (prev + m + 1) = ents[m]?)
    (hg : (lc = none → uint.nat g ≤ s.dur.1) ∧ (∀ v, lc = some v → uint.nat g ≤ Min.min lci v))
    (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc s -∗ stVS rc D g -∗
      pendHyps γ i s (.fstore prev pt ents lci j lc) -∗
      (∀ d : Nat × Nat, ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s with log := s.log ++ ents.drop j, dur := d } -∗ stVS rc D g -∗
        ⌜s.dur.1 ≤ d.1 ∧ uint.nat g ≤ d.1 ∧
          (∀ v, lc = some v → d.1 = Max.max s.dur.1 (Min.min lci v)) ∧ (lc = none → d = s.dur)⌝ -∗
        (∀ v, ⌜lc = some v⌝ -∗ durLb γ i (Min.min lci v)) ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |==> (logWin γ rc i (.store (prev + k + 1) (ents.drop k)) ∗
      (logWin γ rc i (.store (prev + k + 1) (ents.drop k)) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (rc.ownL (A.store (prev + k + 1) (ents.drop k)) ={∅, ⊤ \ ↑storeN}=∗ Ψ))) := by
  iintro #HI #Hd Hpw Hv Hst Hh Hk
  imod (winRes_make γ rc i s (.fstore prev pt ents lci j lc) D g ⟨hpre, hg⟩ rfl) $$ [Hpw Hv Hst Hh] with ⟨HW, Hpw, Hq, Hsq⟩
  · iframe
  imodintro
  isplitl [HW]
  · iunfold logWin; ileft; iexists s, (Pend.fstore prev pt ents lci j lc); iframe HW; ipureintro
    exact ⟨k, hk.1, rfl, hk.2⟩
  iintro HW
  iunfold logWin at HW
  icases HW with (⟨%s', %p', %hok, HW⟩ | ⟨%mn, %mx, %hop, -⟩)
  rotate_left
  · cases hop
  ihave ⟨%heq, Hpw, Hv, Hst, Hh, -⟩ := winRes_back γ rc i s s' (.fstore prev pt ents lci j lc) p' D g rfl $$ [HW Hpw Hq Hsq]
  · iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hpw := ghostVar_update (none : Option Pend) rc.dur.pw (some (Pend.fstore prev pt ents lci j lc)) $$ Hpw
  iapply (logWrite_au γ rc i (fun A => A.store (prev + k + 1) (ents.drop k))
    iprop(srvV rc s' ∗ stVS rc D g ∗ pendHyps γ i s' (.fstore prev pt ents lci j lc) ∗ (|==> ghostVar rc.dur.pw 1 (none : Option Pend)) ∗
      (∀ d : Nat × Nat, ghostVar rc.dur.pw 1 (none : Option Pend) -∗
        srvV rc { s' with log := s'.log ++ ents.drop j, dur := d } -∗ stVS rc D g -∗
        ⌜s'.dur.1 ≤ d.1 ∧ uint.nat g ≤ d.1 ∧
          (∀ v, lc = some v → d.1 = Max.max s'.dur.1 (Min.min lci v)) ∧ (lc = none → d = s'.dur)⌝ -∗
        (∀ v, ⌜lc = some v⌝ -∗ durLb γ i (Min.min lci v)) ={⊤ \ ↑storeN}=∗ Ψ)) Ψ) $$ Hd [Hv Hst Hh Hpw Hk]
  · iframe
  iintro %X Hc ⟨Hv, Hst, Hh, Hpw, Hk⟩
  imod Hpw
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s' $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  obtain ⟨hD, hstg⟩ := Hag2
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  iunfold pendHyps at Hh
  icases Hh with #Hae
  obtain ⟨hpm, hmu, hcase, hlcv⟩ := hpre
  have hlog : logOk (X.A.store (prev + k + 1) (ents.drop k)) (s'.log ++ ents.drop j) X.lo :=
    logOk_fstore X.A s'.log ents X.lo prev j k hlo hk.1 hk.2 hcase
  have hpmm : prevMatch (s'.log ++ ents.drop j) prev pt ∧
      matchedUpTo (s'.log ++ ents.drop j) prev ents ents.length := by
    rcases hcase with ⟨hjl, hlen⟩ | ⟨hj, hlen⟩
    · exact crash_matched_store s'.log prev pt ents j hpm hmu hlen (by omega)
    · subst hj; rw [List.drop_length, List.append_nil]; exact ⟨hpm, hmu⟩
  obtain ⟨hpm', hmu'⟩ := hpmm
  ihave Hol : |={(⊤ \ ↑storeN) \ ↑durN}=> (srvOwn γ i { s' with log := s'.log ++ ents.drop j } ∗
      logCouple γ i (s'.log ++ ents.drop j)) $$ [Ho Hlc]
  · rcases hcase with ⟨hjl, hlen⟩ | ⟨hj, hlen⟩
    · iapply (gprot.followerStore_upd γ _ crash_gprot_store i s' prev pt ents lci j ⟨hpm, hmu, hjl, hlen⟩)
      iframe; iframe #
    · subst hj
      rw [List.drop_length, List.append_nil, show ({ s' with log := s'.log } : SState) = s' from rfl]
      imodintro; iframe
  imod Hol with ⟨Ho, Hlc⟩
  rcases lc with _ | v
  · unfold srvV
    imod (ghostVar_update_halves ({ s' with log := s'.log ++ ents.drop j, dur := s'.dur }, (none : Option TermPend), (none : Option DiscPend))
      rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
    imodintro
    iexists ({ X with s := { s' with log := s'.log ++ ents.drop j, dur := s'.dur }, A := X.A.store (prev + k + 1) (ents.drop k), tp := none })
    isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
    · iunfold durCore
      dsimp only
      try rw [hdp]
      rw [LogAbs.store_staged, LogAbs.store_ci]
      simp only [tpRes, dpRes]
      iframe
      ipureintro
      try simp only [and_true]
      refine ⟨hlog, hlc, hvm, htd, ?_, q2_step _ _ _ _ _ _ _ _ (Nat.le_refl _) (fun x st _ h => prevMatch_append _ _ _ _ h) hci.2.1, hci.2.2.1, (by simp), (by simp)⟩
      rw [hstg]; exact hg.1 rfl
    isplitl []
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl, by first | rfl | exact hdp⟩
    ihave HΨ := Hk $$ %s'.dur Hpw Hv Hst [] []
    · ipureintro
      exact ⟨Nat.le_refl _, hg.1 rfl, ⟨fun v h => (by cases h), fun _ => rfl⟩⟩
    · iintro %v %h; cases h
    iexact HΨ
  · obtain ⟨hv1, hv2⟩ := hlcv v rfl
    imod (gprot.learnCommitFollower γ _ crash_gprot_store i { s' with log := s'.log ++ ents.drop j } prev pt ents lci v
      ⟨hpm', hmu', hv1, hv2⟩) $$ [HI Ho Hdv Hae] with ⟨%d, Ho, Hdv, #Hlb, %hd⟩
    · iframe #; try iframe
    dsimp only at hd
    unfold srvV
    imod (ghostVar_update_halves ({ s' with log := s'.log ++ ents.drop j, dur := d }, (none : Option TermPend), (none : Option DiscPend))
      rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
    imodintro
    iexists ({ X with s := { s' with log := s'.log ++ ents.drop j, dur := d }, A := X.A.store (prev + k + 1) (ents.drop k), tp := none })
    isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
    · iunfold durCore
      dsimp only
      try rw [hdp]
      rw [LogAbs.store_staged, LogAbs.store_ci]
      simp only [tpRes, dpRes]
      iframe
      ipureintro
      try simp only [and_true]
      refine ⟨hlog, hlc, hvm, htd, ?_, q2_step _ _ _ _ _ _ _ _ (by omega) (fun x st _ h => prevMatch_append _ _ _ _ h) hci.2.1, hci.2.2.1, (by simp), (by simp)⟩
      rw [hstg]; have := hg.2 v rfl; omega
    isplitl []
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl, by first | rfl | exact hdp⟩
    ihave HΨ := Hk $$ %d Hpw Hv Hst [] []
    · ipureintro
      have := hg.2 v rfl
      refine ⟨by omega, by omega, ⟨fun v' h => (by cases h; exact hd), fun h => (by cases h)⟩⟩
    · iintro %v' %h; cases h; iexact Hlb
    iexact HΨ

/-- (R2) `storeLogs_fstore_win_k` at `k = j` (no overlap). -/
theorem storeLogs_fstore_win (s : SState) (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (lc : Option Nat) (D : StableAbs) (g : w64)
    (hpre : pendPre γ i s (.fstore prev pt ents lci j lc))
    (hg : (lc = none → uint.nat g ≤ s.dur.1) ∧ (∀ v, lc = some v → uint.nat g ≤ Min.min lci v))
    (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc s -∗ stVS rc D g -∗
      pendHyps γ i s (.fstore prev pt ents lci j lc) -∗
      (∀ d : Nat × Nat, ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s with log := s.log ++ ents.drop j, dur := d } -∗ stVS rc D g -∗
        ⌜s.dur.1 ≤ d.1 ∧ uint.nat g ≤ d.1 ∧
          (∀ v, lc = some v → d.1 = Max.max s.dur.1 (Min.min lci v)) ∧ (lc = none → d = s.dur)⌝ -∗
        (∀ v, ⌜lc = some v⌝ -∗ durLb γ i (Min.min lci v)) ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |==> (logWin γ rc i (.store (prev + j + 1) (ents.drop j)) ∗
      (logWin γ rc i (.store (prev + j + 1) (ents.drop j)) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (rc.ownL (A.store (prev + j + 1) (ents.drop j)) ={∅, ⊤ \ ↑storeN}=∗ Ψ))) :=
  storeLogs_fstore_win_k γ rc i s prev pt ents lci j j lc D g hpre
    ⟨Nat.le_refl _, fun m h1 h2 => absurd h2 (by omega)⟩ hg Ψ

/-- (R2) **The follower's truncation** at `DeleteRange(prev + 1 + j, |s.log|)`'s commit
(`truncate_upd`). -/
theorem deleteRange_trunc_win (s : SState) (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (D : StableAbs) (g : w64) (hpre : pendPre γ i s (.trunc prev pt ents lci j)) (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc s -∗ stVS rc D g -∗
      pendHyps γ i s (.trunc prev pt ents lci j) -∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s with log := s.log.take (prev + j) } -∗
        stVS rc D g -∗ ⌜s.dur.1 < prev + 1 + j⌝ ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |==> (logWin γ rc i (.del true (prev + 1 + j) s.log.length) ∗
      (logWin γ rc i (.del true (prev + 1 + j) s.log.length) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (∀ hi' : w64, rc.ownL (A.delete (prev + 1 + j) s.log.length hi')
          ={∅, ⊤ \ ↑storeN}=∗ Ψ))) := by
  iintro #HI #Hd Hpw Hv Hst Hh Hk
  iunfold pendHyps at Hh
  icases Hh with #Hh
  imod (winRes_make γ rc i s (.trunc prev pt ents lci j) D g ⟨hpre, trivial⟩ rfl) $$ [Hpw Hv Hst] with ⟨HW, Hpw, Hq, Hsq⟩
  · iunfold pendHyps; iframe; iexact Hh
  imodintro
  isplitl [HW]
  · iunfold logWin; ileft; iexists s, (Pend.trunc prev pt ents lci j); iframe HW; ipureintro; rfl
  iintro HW
  iunfold logWin at HW
  icases HW with (⟨%s', %p', %hok, HW⟩ | ⟨%mn, %mx, %hop, -, -, #Hlb⟩)
  rotate_left
  · cases hop
  ihave ⟨%heq, Hpw, Hv, Hst, Hh, -⟩ := winRes_back γ rc i s s' (.trunc prev pt ents lci j) p' D g rfl $$ [HW Hpw Hq Hsq]
  · iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hpw := ghostVar_update (none : Option Pend) rc.dur.pw (some (Pend.trunc prev pt ents lci j)) $$ Hpw
  iapply (logDelete_au γ rc i (prev + 1 + j) s'.log.length
    iprop(srvV rc s' ∗ stVS rc D g ∗ pendHyps γ i s' (.trunc prev pt ents lci j) ∗ (|==> ghostVar rc.dur.pw 1 (none : Option Pend)) ∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s' with log := s'.log.take (prev + j) } -∗
        stVS rc D g -∗ ⌜s'.dur.1 < prev + 1 + j⌝ ={⊤ \ ↑storeN}=∗ Ψ)) Ψ) $$ Hd [Hv Hst Hh Hpw Hk]
  · iframe
  iintro %X %hi' Hc ⟨Hv, Hst, Hh, Hpw, Hk⟩
  imod Hpw
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s' $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  obtain ⟨hD, hstg⟩ := Hag2
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  iunfold pendHyps at Hh
  icases Hh with #Hae
  imod (gprot.truncate_upd γ _ crash_gprot_store i s' prev pt ents lci j hpre) $$ [HI Ho Hlc Hae]
    with ⟨Ho, Hlc, %hdur⟩
  · iframe #; try iframe
  unfold srvV
  imod (ghostVar_update_halves ({ s' with log := s'.log.take (prev + j) }, (none : Option TermPend), (none : Option DiscPend))
    rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imodintro
  iexists ({ X with s := { s' with log := s'.log.take (prev + j) }, A := X.A.delete (prev + 1 + j) s'.log.length hi', tp := none })
  isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
  · iunfold durCore
    dsimp only
    try rw [hdp]
    rw [LogAbs.delete_staged, LogAbs.delete_ci]
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨?_, hlc, hvm, htd, ⟨hci.1, q2_step _ _ _ _ _ _ _ _ (Nat.le_refl _) (fun x st hx h => prevMatch_take _ _ _ _ (by omega) h) hci.2.1, hci.2.2.1, (by simp), (by simp)⟩⟩
    rw [show prev + 1 + j = (prev + j) + 1 by omega]
    exact logOk_delete _ _ _ _ _ _ hlo (Nat.le_refl _)
  isplitl []
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, by first | rfl | exact hdp⟩
  ihave HΨ := Hk $$ Hpw Hv Hst [] 
  · ipureintro; exact hdur
  iexact HΨ

/-- (R2, for R4b/R5) **An install's discard** at `DeleteRange(1, mx)`'s commit (`installDiscard_core`):
the log becomes the committed prefix of length `d.x` (`mx` at least the log's last index, so the
store is emptied), the snapshot store's record moves from the discard-pending case to the durable
one (its `lastApplied` half, `a ≤ d.x`, goes back to the caller), the frontier to `d.x`. Takes the
main goroutine's half of the pending-install record (none: the restore answered). -/
theorem deleteRange_discard_win (s : SState) (d : DiscPend) (D : StableAbs) (g : w64) (mx c0 : Nat)
    (hpre : pendPre γ i s (.discard d)) (hmx : s.log.length ≤ mx) (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvVP rc s none (some d) -∗
      stVS rc D g -∗ pendHyps γ i s (.discard d) -∗ ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) -∗
      monoNatAuthOwn rc.dur.comp (1 : Qp).half c0 -∗ latLb rc d.x -∗ applLb rc d.x -∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ ∀ s' : SState, srvV rc s' -∗ stVS rc D g -∗
        ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) -∗
        monoNatAuthOwn rc.dur.comp (1 : Qp).half d.x -∗ durLb γ i d.x -∗
        ⌜s'.log.length = d.x ∧ lastTerm s'.log = d.st ∧ s'.dur.1 = d.x ∧ s'.term = s.term ∧
          s'.vterm = s.vterm ∧ s'.vcand = s.vcand ∧ s'.cidx = s.cidx⌝ -∗
        ([∗list] k ↦ e ∈ s'.log, CIdx γ (k + 1) e) -∗
        (∃ a : Nat, monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ d.x⌝) ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |==> (logWin γ rc i (.del true 1 mx) ∗
      (logWin γ rc i (.del true 1 mx) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (∀ hi' : w64, rc.ownL (A.delete 1 mx hi') ={∅, ⊤ \ ↑storeN}=∗ Ψ))) := by
  iintro #HI #Hd Hpw Hv Hst Hh Hpe Hcm #Hll #Happ Hk
  imod (winRes_makeP γ rc i s (.discard d) D g ⟨hpre, trivial⟩) $$ [Hpw Hv Hst Hh] with ⟨HW, Hpw, Hq, Hsq⟩
  · iframe
  imodintro
  isplitl [HW]
  · iunfold logWin; ileft; iexists s, (Pend.discard d); iframe HW; ipureintro; exact ⟨1, mx, rfl⟩
  iintro HW
  iunfold logWin at HW
  icases HW with (⟨%s', %p', %hok, HW⟩ | ⟨%mn, %mx', %hop, -⟩)
  rotate_left
  · cases hop
  ihave ⟨%heq, Hpw, Hv, Hst, Hh, -⟩ := winRes_backP γ rc i s s' (.discard d) p' D g $$ [HW Hpw Hq Hsq]
  · iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hpw := ghostVar_update (none : Option Pend) rc.dur.pw (some (Pend.discard d)) $$ Hpw
  iintro Hnc
  imod (durOpen γ rc i crash_dur_storeN) $$ Hd Hnc with ⟨Hnc, %X, Hc, Hs, Hcl⟩
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hlat⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN from Iris.Std.LawfulSet.empty_subset)
  iintro Hmask
  iframe Hnc
  inext
  iexists X.A
  iframe HL
  iintro %hi' HL
  imod Hmask
  imod Hpw
  -- the main goroutine's views agree with the crash state
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvVP_agree γ rc i X s' none (some d) $$ [Hc Hv]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla, Hbp⟩
  icombine Hpend Hpe gives %hpe
  have hpe' : X.pend = none := hpe.2
  obtain ⟨hlo, hlc, hvm, htd, hci, ⟨⟨hdl, hpd, hll⟩, hcd, hq5a, hq5b⟩⟩ := Hp
  have hmb := hq5b d hdp
  obtain ⟨m, b, hlm, hmi, hmt⟩ := hmb
  -- the store is emptied: every stored index is an entry of the log, in `1..mx`
  have hempty : (X.A.delete 1 mx hi').m = ∅ := by
    rw [LogAbs.delete_m]
    apply GMap.ext
    intro k
    rw [crash_lookup_del, GMap.lookup_empty]
    split
    · rfl
    · rename_i hr
      rcases hk : X.A.m.lookup k with _ | e
      · rfl
      · have he := hlo.1 k e hk
        rw [hs] at he
        have := gprot.ent_pos he
        have := gprot.ent_le_length he
        exact absurd ⟨by omega, by omega⟩ hr
  -- the snapshot store's record: the discard pending, with the caller's `lastApplied` half
  unfold latestDur
  icases Hlat with ⟨Hlok, Hbr⟩
  rw [hpe']
  icases Hbr with (%hn | ⟨%m', %b', %hl', (⟨-, %hdn⟩ | ⟨#Hsf, %hdpd, Happl⟩)⟩)
  · rw [hlm] at hn; cases hn
  · rw [hdp] at hdn; cases hdn
  -- the discard on the core
  icases Happl with ⟨%a, Happl, %ha⟩
  have hax : a ≤ d.x := by
    obtain ⟨ℓ, hℓ⟩ := hdpd
    rw [hdp] at hℓ
    cases hℓ
    exact ha
  ihave Hc : durCore γ rc i X $$ [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla Hbp]
  · iunfold durCore
    rw [hpe']
    iframe
    ipureintro
    exact ⟨hlo, hlc, hvm, htd, hci, ⟨⟨hdl, fun x st id h => (by cases h), hll⟩, hcd, hq5a, hq5b⟩⟩
  try rw [hs]
  imod (installDiscard_core γ rc i crash_gprot_store X s' d (X.A.delete 1 mx hi') c0
    ⟨hs, hdp, hpe'⟩ ⟨hempty, rfl, rfl⟩) $$ [HI Hc Hv Hcm Hll Happ]
    with ⟨%X', Hc', Hv', Hcm, #Hlbx, HC, %hX'⟩
  · rw [htp]; iframe; iframe #
  obtain ⟨hA', hD', hlat', hpend', hdp', hc', hlo', hlen, hlt, hdur, hterm, hvt, hvc, hcx⟩ := hX'
  -- the record moves to the durable case
  ihave Hpe2 : ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) $$ [Hpe]
  · iexact Hpe
  imod Hcl $$ %X' Hc' [HL HS HSS Hlok] with -
  · iunfold durStores
    rw [hA', hD', hlat', hpend', hdp']
    inext
    iframe
    unfold latestDur
    rw [hpe']
    iframe Hlok
    iright
    iexists m, b
    isplitl []
    · ipureintro; exact hlm
    ileft
    rw [hmi]
    iframe Hlbx
    ipureintro; rfl
  rw [htp]
  ihave HΨ := Hk $$ Hpw %X'.s [Hv'] Hst Hpe2 Hcm Hlbx [] HC [Happl]
  · unfold srvV; unfold srvVP; iexact Hv'
  · ipureintro; exact ⟨hlen, hlt, hdur, hterm, hvt, hvc, hcx⟩
  · iexists a; iframe Happl; ipureintro; exact hax
  iexact HΨ

/-- (R2) **`SetUint64(CurrentTerm, t)`'s commit** (`setCurrentTerm`): no model step; the term step
recorded pending (`tp`, its `tpRes` moved into the crash state), fired at the atomic store
(`setTerm_R`/`electTerm_R`). `tv` the written value: `t` (`.set t`) or `s.term + 1` (`.elect`). -/
theorem setUint64_term_win (s : SState) (tp : TermPend) (tv : Nat) (D : StableAbs) (g : w64)
    (ht : (tp = .set tv ∧ s.term ≤ tv) ∨ (tp = .elect ∧ tv = s.term + 1)) (h64 : tv < 2 ^ 64)
    (Ψ : IProp GF) :
    srvDurInv γ rc i -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc s -∗ stVS rc D g -∗ tpRes γ (some tp) -∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvVP rc s (some tp) none -∗
        stVS rc { D with ints := D.ints.insert (go!"CurrentTerm" : List w8) (W64 tv) } g
          ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |==> (stWin γ rc i (.setU (go!"CurrentTerm" : List w8) (W64 tv)) ∗
      (stWin γ rc i (.setU (go!"CurrentTerm" : List w8) (W64 tv)) -∗
        |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D0 : StableAbs, rc.ownS D0 ∗
          (rc.ownS { D0 with ints := D0.ints.insert (go!"CurrentTerm" : List w8) (W64 tv) }
            ={∅, ⊤ \ ↑storeN}=∗ Ψ))) := by
  iintro #Hd Hpw Hv Hst Htp Hk
  have hpre : pendPre γ i s (.term tp) := by
    rcases ht with ⟨rfl, h⟩ | ⟨rfl, _⟩
    · exact h
    · trivial
  imod (winRes_make γ rc i s (.term tp) D g ⟨hpre, trivial⟩ rfl) $$ [Hpw Hv Hst Htp] with ⟨HW, Hpw, Hq, Hsq⟩
  · iunfold pendHyps; iframe
  imodintro
  isplitl [HW]
  · iunfold stWin; ileft; iexists s, (Pend.term tp); iframe HW; ipureintro
    rcases ht with ⟨rfl, _⟩ | ⟨rfl, rfl⟩ <;> rfl
  iintro HW
  iunfold stWin at HW
  icases HW with (⟨%s', %p', %hok, HW⟩ | ⟨%vb, %hop⟩ | ⟨%kb, %v, %D', %g', %hop, Hq3, Hpw3⟩)
  rotate_left
  · cases hop
  · icombine Hpw3 Hpw gives %h
    exact absurd h.2 (by simp)
  ihave ⟨%heq, Hpw, Hv, Hst, Htp, -⟩ := winRes_back γ rc i s s' (.term tp) p' D g rfl $$ [HW Hpw Hq Hsq]
  · iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hpw := ghostVar_update (none : Option Pend) rc.dur.pw (some (Pend.term tp)) $$ Hpw
  iapply (stableWrite_au γ rc i (fun D0 => { D0 with ints := D0.ints.insert (go!"CurrentTerm" : List w8) (W64 tv) })
    iprop(srvV rc s' ∗ stVS rc D g ∗ pendHyps γ i s' (.term tp) ∗ (|==> ghostVar rc.dur.pw 1 (none : Option Pend)) ∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvVP rc s' (some tp) none -∗
        stVS rc { D with ints := D.ints.insert (go!"CurrentTerm" : List w8) (W64 tv) } g ={⊤ \ ↑storeN}=∗ Ψ)) Ψ) $$ Hd [Hv Hst Htp Hpw Hk]
  · iframe
  iintro %X Hc ⟨Hv, Hst, Htp, Hpw, Hk⟩
  imod Hpw
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s' $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  obtain ⟨hD, hstg⟩ := Hag2
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, -, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  iunfold pendHyps at Htp
  unfold srvV srvVP stVS
  imod (ghostVar_update_halves (s', some tp, (none : Option DiscPend)) rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imod (ghostVar_update_halves ({ X.D with ints := X.D.ints.insert (go!"CurrentTerm" : List w8) (W64 tv) }, X.A.staged) rc.dur.st _ _)
    $$ Hst0 Hst with ⟨Hst0, Hst⟩
  have htv : uint.nat (W64 tv) = tv := by word
  imodintro
  iexists ({ X with D := { X.D with ints := X.D.ints.insert (go!"CurrentTerm" : List w8) (W64 tv) }, tp := some tp })
  isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
  · iunfold durCore
    dsimp only
    rw [hs]
    try rw [hdp]
    simp only [dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨hlo, hlc, ?_, ?_, ⟨hci.1, hci.2.1, hci.2.2.1, (by simp), (by simp)⟩⟩
    · unfold voteMatches at hvm ⊢
      rw [gprot.lookup_ins, if_neg (by decide)]
      exact hvm
    · unfold termDurOk
      rw [gprot.lookup_ins, if_pos rfl]
      simp only [Option.getD_some]
      rcases ht with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨_, rfl, htv, h⟩)
      · exact Or.inr (Or.inr ⟨rfl, htv⟩)
  isplitl []
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, by first | rfl | exact hdp⟩
  rw [hD, hstg]
  dsimp only
  ihave HΨ := Hk $$ Hpw Hv Hst
  iexact HΨ

/-- (R2) **`Set(LastVoteCand, c)`'s commit** (`persistVote`'s first write, after fix 3): no step
(`voteMatches` holds by `s.vterm < s.term`); the window is `stWin`'s right disjunct. -/
theorem set_voteCand_win (s : SState) (D : StableAbs) (g : w64) (c : List w8)
    (hv : s.vterm < s.term) (Ψ : IProp GF) :
    srvDurInv γ rc i -∗ srvV rc s -∗ stVS rc D g -∗
      (srvV rc s -∗ stVS rc { D with bytes := D.bytes.insert (go!"LastVoteCand" : List w8) c } g
        ={⊤ \ ↑storeN}=∗ Ψ) -∗
      stWin γ rc i (.set (go!"LastVoteCand" : List w8) c) ∗
      (stWin γ rc i (.set (go!"LastVoteCand" : List w8) c) -∗
        |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D0 : StableAbs, rc.ownS D0 ∗
          (rc.ownS { D0 with bytes := D0.bytes.insert (go!"LastVoteCand" : List w8) c }
            ={∅, ⊤ \ ↑storeN}=∗ Ψ)) := by
  iintro #Hd Hv Hst Hk
  isplitl []
  · iunfold stWin; iright; ileft; iexists c; ipureintro; rfl
  iintro -
  iapply (stableWrite_au γ rc i (fun D0 => { D0 with bytes := D0.bytes.insert (go!"LastVoteCand" : List w8) c })
    iprop(srvV rc s ∗ stVS rc D g ∗
      (srvV rc s -∗ stVS rc { D with bytes := D.bytes.insert (go!"LastVoteCand" : List w8) c } g ={⊤ \ ↑storeN}=∗ Ψ)) Ψ)
    $$ Hd [Hv Hst Hk]
  · iframe
  iintro %X Hc ⟨Hv, Hst, Hk⟩
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  obtain ⟨hD, hstg⟩ := Hag2
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  unfold stVS
  imod (ghostVar_update_halves ({ X.D with bytes := X.D.bytes.insert (go!"LastVoteCand" : List w8) c }, X.A.staged) rc.dur.st _ _)
    $$ Hst0 Hst with ⟨Hst0, Hst⟩
  imodintro
  iexists ({ X with D := { X.D with bytes := X.D.bytes.insert (go!"LastVoteCand" : List w8) c } })
  isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
  · iunfold durCore
    dsimp only
    try rw [hs]
    try rw [htp]
    try rw [hdp]
    iframe
    ipureintro
    refine ⟨hlo, hlc, ?_, ?_, ⟨hci.1, hci.2.1, hci.2.2.1, (by simp), (by simp)⟩⟩
    · unfold voteMatches at hvm ⊢
      exact ⟨hvm.1, Or.inr (Or.inl hv)⟩
    · unfold termDurOk at htd ⊢
      exact htd
  isplitl []
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, by first | rfl | exact hdp⟩
  rw [hD, hstg]
  dsimp only
  ihave HΨ := Hk $$ Hv Hst
  iexact HΨ

/-- (R2) **`SetUint64(LastVoteTerm, s.term)`'s commit** (`persistVote`'s second write): the vote
(`grantVote_upd`), `LastVoteCand = c` already stored. -/
theorem setUint64_vote_win (s : SState) (c : SID) (li lt : Nat) (D : StableAbs) (g : w64)
    (hpre : pendPre γ i s (.vote c li lt))
    (hc : D.bytes.lookup (go!"LastVoteCand" : List w8) = some c) (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc s -∗ stVS rc D g -∗ candIs γ c s.term li lt -∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s with vterm := s.term, vcand := c } -∗
        stVS rc { D with ints := D.ints.insert (go!"LastVoteTerm" : List w8) (W64 s.term) } g -∗
        voteIs γ i s.term c ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |==> (stWin γ rc i (.setU (go!"LastVoteTerm" : List w8) (W64 s.term)) ∗
      (stWin γ rc i (.setU (go!"LastVoteTerm" : List w8) (W64 s.term)) -∗
        |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D0 : StableAbs, rc.ownS D0 ∗
          (rc.ownS { D0 with ints := D0.ints.insert (go!"LastVoteTerm" : List w8) (W64 s.term) }
            ={∅, ⊤ \ ↑storeN}=∗ Ψ))) := by
  iintro #HI #Hd Hpw Hv Hst Hcand Hk
  imod (winRes_make γ rc i s (.vote c li lt) D g ⟨hpre, hc⟩ rfl) $$ [Hpw Hv Hst Hcand] with ⟨HW, Hpw, Hq, Hsq⟩
  · iunfold pendHyps; iframe
  imodintro
  isplitl [HW]
  · iunfold stWin; ileft; iexists s, (Pend.vote c li lt); iframe HW; ipureintro; rfl
  iintro HW
  iunfold stWin at HW
  icases HW with (⟨%s', %p', %hok, HW⟩ | ⟨%vb, %hop⟩ | ⟨%kb, %v, %D', %g', %hop, Hq3, Hpw3⟩)
  rotate_left
  · cases hop
  · icombine Hpw3 Hpw gives %h
    exact absurd h.2 (by simp)
  ihave ⟨%heq, Hpw, Hv, Hst, Hcand, -⟩ := winRes_back γ rc i s s' (.vote c li lt) p' D g rfl $$ [HW Hpw Hq Hsq]
  · iframe
  obtain ⟨rfl, rfl⟩ := heq
  ihave Hpw := ghostVar_update (none : Option Pend) rc.dur.pw (some (Pend.vote c li lt)) $$ Hpw
  iapply (stableWrite_au γ rc i (fun D0 => { D0 with ints := D0.ints.insert (go!"LastVoteTerm" : List w8) (W64 s'.term) })
    iprop(srvV rc s' ∗ stVS rc D g ∗ pendHyps γ i s' (.vote c li lt) ∗ (|==> ghostVar rc.dur.pw 1 (none : Option Pend)) ∗
      (ghostVar rc.dur.pw 1 (none : Option Pend) -∗ srvV rc { s' with vterm := s'.term, vcand := c } -∗
        stVS rc { D with ints := D.ints.insert (go!"LastVoteTerm" : List w8) (W64 s'.term) } g -∗
        voteIs γ i s'.term c ={⊤ \ ↑storeN}=∗ Ψ)) Ψ) $$ Hd [Hv Hst Hcand Hpw Hk]
  · iframe
  iintro %X Hc ⟨Hv, Hst, Hcand, Hpw, Hk⟩
  imod Hpw
  ihave ⟨Hc, Hv, %Hag⟩ := durCore_srvV_agree γ rc i X s' $$ [Hc Hv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hs, htp, hdp⟩ := Hag
  obtain ⟨hD, hstg⟩ := Hag2
  iunfold durCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst0, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp, Hla⟩
  rw [hs, htp, hdp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  iunfold pendHyps at Hcand
  imod (gprot.srvOwn_facts γ _ crash_gprot_store i s') $$ [HI Ho] with ⟨Ho, -, %hf⟩
  · iframe #; try iframe
  imod (gprot.grantVote_upd γ _ crash_gprot_store i c s' li lt hpre.1 hpre.2) $$ [HI Ho Hcand]
    with ⟨Ho, #Hvote⟩
  · iframe #; try iframe
  unfold srvV stVS
  imod (ghostVar_update_halves ({ s' with vterm := s'.term, vcand := c }, (none : Option TermPend), (none : Option DiscPend))
    rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imod (ghostVar_update_halves ({ X.D with ints := X.D.ints.insert (go!"LastVoteTerm" : List w8) (W64 s'.term) }, X.A.staged) rc.dur.st _ _)
    $$ Hst0 Hst with ⟨Hst0, Hst⟩
  have hT : uint.nat (W64 s'.term) = s'.term := by have := hf.2.2.2.2.2.1; word
  imodintro
  iexists ({ X with s := { s' with vterm := s'.term, vcand := c }, D := { X.D with ints := X.D.ints.insert (go!"LastVoteTerm" : List w8) (W64 s'.term) }, tp := none })
  isplitl [Ho Hdv Hlc Htc Hcc Hsv Hst0 Htv Hcv Hcomp Hpend Htp Hdp Hla]
  · iunfold durCore
    dsimp only
    try rw [hdp]
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨hlo, hlc, ?_, ?_, ⟨hci.1, hci.2.1, hci.2.2.1, (by simp), (by simp)⟩⟩
    · unfold voteMatches
      rw [gprot.lookup_ins, if_pos rfl]
      simp only [Option.getD_some]
      refine ⟨hT, Or.inr (Or.inr ?_)⟩
      rw [hD]; exact hc
    · unfold termDurOk at htd ⊢
      rw [gprot.lookup_ins, if_neg (by decide)]
      exact htd
  isplitl []
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, by first | rfl | exact hdp⟩
  rw [hD, hstg]
  dsimp only
  ihave HΨ := Hk $$ Hpw Hv Hst Hvote
  iexact HΨ

end commits

/-! ## The crash: firing a surviving window, the next generation's vacant state -/

section dead

/-- (R2) A store's coupling depends only on its entries. -/
theorem logOk_m (A A' : LogAbs) (L : RLog) (lo : Nat) (h : A'.m = A.m) : logOk A' L lo ↔ logOk A L lo := by
  unfold logOk; rw [h]

/-- (R2) The term a pending term step writes. -/
def termPendVal (s : SState) : TermPend → Nat
  | .set t => t
  | .elect => s.term + 1

/-- (R2) **What a write that fires `p` from `s` leaves in the stores** (`A'`, `D'`, against the dead
state's `X.A`, `X.D`): what the store's crash lemma must say of the surviving image, the write's op
(`pendLogOk`/`pendStOk`) applied (the stores' volatile parts, `hi` and `staged`, are not
constrained; an install's discard leaves the store empty, R5 Q4). -/
def pendStoreOk (p : Pend) (s : SState) (X : SrvDur) (A' : LogAbs) (D' : StableAbs) : Prop :=
  match p with
  | .app es => A'.m = LogAbs.ins X.A.m (s.log.length + 1) es ∧ A'.ci = X.A.staged ∧ D' = X.D
  | .cfg e _ _ => A'.m = LogAbs.ins X.A.m (s.log.length + 1) [e] ∧ A'.ci = X.A.staged ∧ D' = X.D
  | .fstore prev _ ents _ j _ => (∃ k, k ≤ j ∧ (∀ m, k ≤ m → m < j → ent s.log (prev + m + 1) = ents[m]?) ∧
      A'.m = LogAbs.ins X.A.m (prev + k + 1) (ents.drop k)) ∧ A'.ci = X.A.staged ∧ D' = X.D
  | .trunc prev _ _ _ j => A'.m = LogAbs.del X.A.m (prev + 1 + j) s.log.length ∧
      A'.ci = X.A.ci ∧ D' = X.D
  | .discard _ => A'.m = ∅ ∧ A'.ci = X.A.ci ∧ D' = X.D
  | .vote _ _ _ => A'.m = X.A.m ∧ A'.ci = X.A.ci ∧
      D' = { X.D with ints := X.D.ints.insert (go!"LastVoteTerm" : List w8) (W64 s.term) }
  | .term tp => A'.m = X.A.m ∧ A'.ci = X.A.ci ∧
      D' = { X.D with ints := X.D.ints.insert (go!"CurrentTerm" : List w8) (W64 (termPendVal s tp)) }

/-- (R2, R1 §3: `pend_fire`) **Firing a surviving window**: the window's view agrees with the dead
state's (`s = X.s`), and its step is fired with gprot's law on `deadCore`'s halves, the couplings
re-established against the surviving image `A'`, `D'` (`pendStoreOk`). A term write's step is only
recorded (`tp`), fired by `dead_vacant`. -/
theorem dead_fire {E : CoPset} (hE : ↑gprotN ⊆ E)
    (p : Pend) (s : SState) (X : SrvDur) (A' : LogAbs) (D' : StableAbs)
    (hst : pendStoreOk p s X A' D') :
    Inv γ ∗ srvDead γ rc i X ∗ winRes γ rc i s p ⊢ |={E}=> ∃ X' : SrvDur, deadCore γ rc i X' ∗
      ⌜X'.A.m = A'.m ∧ X'.A.ci = A'.ci ∧ X'.D = D' ∧ X'.lat = X.lat⌝ := by
  unfold srvDead
  iintro ⟨#HI, ⟨Hc, Hsv, Hst⟩, HW⟩
  iunfold winRes at HW
  icases HW with ⟨-, Hq, ⟨%D0, %g0, Hsq, %hwp⟩, Hh, %hpre⟩
  unfold srvVPq stVq
  icombine Hsv Hq gives %h1
  icombine Hst Hsq gives %h2
  have e1 := h1.2
  have e2 := h2.2
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨hs, htp, hdp⟩ := e1
  obtain ⟨hD, hg⟩ := e2
  iunfold deadCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, %Hp, Hlat, Htp, Hdp⟩
  rw [hs, htp] at Hp ⊢
  obtain ⟨hlo, hlc, hvm, htd, hci, hgrp⟩ := Hp
  cases p with
  | app es =>
    simp only [pendDp] at hdp
    rw [hdp] at hgrp ⊢
    obtain ⟨hm, hc, hD'⟩ := hst
    iunfold pendHyps at Hh
    icases Hh with ⟨#Hl, Hr, Hops⟩
    imod (gprot.leaderAppendCmd_upd γ _ hE i s es hpre) $$ [HI Ho Hlc Hl Hr Hops] with ⟨Ho, Hlc, -⟩
    · iframe #; try iframe
    imodintro
    iexists ({ X with s := { s with log := s.log ++ es }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', tp := none })
    iunfold deadCore
    dsimp only
    try rw [hdp]
    rw [hD']
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    refine ⟨⟨?_, hlc, hvm, htd, ?_, by simpa using And.intro (q2_step X.lo X.lat X.pend none s.log (s.log ++ es) s.dur.1 (s.dur.1) (Nat.le_refl _) (fun x st _ h => prevMatch_append _ _ _ _ h) hgrp.1) hgrp.2⟩, by simp, by simp, by simp, by simp⟩
    · have := logOk_store X.A s.log es X.lo hlo
      rw [hm]; exact this
    · rw [hc, hg]; exact hwp
  | cfg e k p' =>
    simp only [pendDp] at hdp
    rw [hdp] at hgrp ⊢
    obtain ⟨hm, hc, hD'⟩ := hst
    iunfold pendHyps at Hh
    icases Hh with ⟨#Hl, Hcf, #Hci, Hr⟩
    imod (gprot.leaderAppendCfg_upd γ _ hE i s e k p' hpre) $$ [HI Ho Hlc Hl Hcf Hci Hr] with ⟨Ho, Hlc, -, -⟩
    · iframe #; try iframe
    imodintro
    iexists ({ X with s := { s with log := s.log ++ [e] }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', tp := none })
    iunfold deadCore
    dsimp only
    try rw [hdp]
    rw [hD']
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    refine ⟨⟨?_, hlc, hvm, htd, ?_, by simpa using And.intro (q2_step X.lo X.lat X.pend none s.log (s.log ++ [e]) s.dur.1 (s.dur.1) (Nat.le_refl _) (fun x st _ h => prevMatch_append _ _ _ _ h) hgrp.1) hgrp.2⟩, by simp, by simp, by simp, by simp⟩
    · have := logOk_store X.A s.log [e] X.lo hlo
      rw [hm]; exact this
    · rw [hc, hg]; exact hwp
  | trunc prev pt ents lci j =>
    simp only [pendDp] at hdp
    rw [hdp] at hgrp ⊢
    obtain ⟨hm, hc, hD'⟩ := hst
    iunfold pendHyps at Hh
    icases Hh with #Hae
    imod (gprot.truncate_upd γ _ hE i s prev pt ents lci j hpre) $$ [HI Ho Hlc Hae] with ⟨Ho, Hlc, %hdur⟩
    · iframe #; try iframe
    imodintro
    iexists ({ X with s := { s with log := s.log.take (prev + j) }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', tp := none })
    iunfold deadCore
    dsimp only
    try rw [hdp]
    rw [hD']
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    refine ⟨⟨?_, hlc, hvm, htd, ?_, by simpa using And.intro (q2_step X.lo X.lat X.pend none s.log (s.log.take (prev + j)) s.dur.1 (s.dur.1) (Nat.le_refl _) (fun x st hx h => prevMatch_take _ _ _ _ (by omega) h) hgrp.1) hgrp.2⟩, by simp, by simp, by simp, by simp⟩
    · have := logOk_delete X.A s.log X.lo (prev + j) s.log.length X.A.hi hlo (Nat.le_refl _)
      rw [hm, show prev + 1 + j = prev + j + 1 by omega]; exact this
    · rw [hc]; exact hci
  | vote c li lt =>
    simp only [pendDp] at hdp
    rw [hdp] at hgrp ⊢
    obtain ⟨hm, hc, hD'⟩ := hst
    iunfold pendHyps at Hh
    imod (gprot.srvOwn_facts γ _ hE i s) $$ [HI Ho] with ⟨Ho, -, %hf⟩
    · iframe #; try iframe
    imod (gprot.grantVote_upd γ _ hE i c s li lt hpre.1 hpre.2) $$ [HI Ho Hh] with ⟨Ho, -⟩
    · iframe #; try iframe
    have hT : uint.nat (W64 s.term) = s.term := by have := hf.2.2.2.2.2.1; word
    imodintro
    iexists ({ X with s := { s with vterm := s.term, vcand := c }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', tp := none })
    iunfold deadCore
    dsimp only
    try rw [hdp]
    rw [hD']
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    refine ⟨⟨(logOk_m X.A _ _ _ hm).2 hlo, hlc, ?_, ?_, by rw [hc]; exact hci, by simpa using hgrp⟩, by simp, by simp, by simp, by simp⟩
    · unfold voteMatches
      rw [gprot.lookup_ins, if_pos rfl]
      simp only [Option.getD_some]
      refine ⟨hT, Or.inr (Or.inr ?_)⟩
      rw [hD]; exact hwp
    · unfold termDurOk at htd ⊢
      rw [gprot.lookup_ins, if_neg (by decide)]
      exact htd
  | term tp =>
    simp only [pendDp] at hdp
    rw [hdp] at hgrp ⊢
    obtain ⟨hm, hc, hD'⟩ := hst
    iunfold pendHyps at Hh
    cases tp with
    | set t =>
      iunfold tpRes at Hh
      imod (gprot.setTerm_upd γ _ hE i s t hpre) $$ [HI Ho Htc Hh] with ⟨Ho, Htc, -⟩
      · iframe #; try iframe
      imod (gprot.srvOwn_facts γ _ hE i { s with term := t }) $$ [HI Ho] with ⟨Ho, -, %hf⟩
      · iframe #; try iframe
      have ht : uint.nat (W64 t) = t := by have := hf.2.2.2.2.2.1; simp only at this; word
      imodintro
      iexists ({ X with s := { s with term := t }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', tp := none })
      iunfold deadCore
      dsimp only
      try rw [hdp]
      rw [hD']
      simp only [tpRes, dpRes]
      iframe
      ipureintro
      refine ⟨⟨(logOk_m X.A _ _ _ hm).2 hlo, hlc, ?_, ?_, by rw [hc]; exact hci, by simpa using hgrp⟩, by simp, by simp, by simp, by simp⟩
      · unfold voteMatches at hvm ⊢
        rw [gprot.lookup_ins, if_neg (by decide)]
        obtain ⟨h1, h2⟩ := hvm
        refine ⟨h1, ?_⟩
        rcases h2 with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by simp only; simp only [pendPre] at hpre; omega))
        · exact Or.inr (Or.inr h)
      · unfold termDurOk
        rw [gprot.lookup_ins, if_pos rfl]
        simp only [Option.getD_some, termPendVal]
        exact Or.inl ⟨trivial, ht⟩
    | elect =>
      iunfold tpRes at Hh
      imod (gprot.electTerm_upd γ _ hE i s) $$ [HI Ho Htc Hh] with ⟨Ho, Htc, -, -, -, -, -⟩
      · iframe #; try iframe
      imod (gprot.srvOwn_facts γ _ hE i { s with term := s.term + 1 }) $$ [HI Ho] with ⟨Ho, -, %hf⟩
      · iframe #; try iframe
      have ht : uint.nat (W64 (s.term + 1)) = s.term + 1 := by have := hf.2.2.2.2.2.1; simp only at this; word
      imodintro
      iexists ({ X with s := { s with term := s.term + 1 }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', tp := none })
      iunfold deadCore
      dsimp only
      try rw [hdp]
      rw [hD']
      simp only [tpRes, dpRes]
      iframe
      ipureintro
      refine ⟨⟨(logOk_m X.A _ _ _ hm).2 hlo, hlc, ?_, ?_, by rw [hc]; exact hci, by simpa using hgrp⟩, by simp, by simp, by simp, by simp⟩
      · unfold voteMatches at hvm ⊢
        rw [gprot.lookup_ins, if_neg (by decide)]
        obtain ⟨h1, h2⟩ := hvm
        refine ⟨h1, ?_⟩
        rcases h2 with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by simp only; omega))
        · exact Or.inr (Or.inr h)
      · unfold termDurOk
        rw [gprot.lookup_ins, if_pos rfl]
        simp only [Option.getD_some, termPendVal]
        exact Or.inl ⟨trivial, ht⟩
  | fstore prev pt ents lci j lc =>
    simp only [pendDp] at hdp
    rw [hdp] at hgrp ⊢
    obtain ⟨⟨k, hkj, hov, hm⟩, hc, hD'⟩ := hst
    iunfold pendHyps at Hh
    icases Hh with #Hae
    obtain ⟨hpm, hmu, hcase, hlcv⟩ := hpre
    have hlog := logOk_fstore X.A s.log ents X.lo prev j k hlo hkj hov hcase
    have hlog' : logOk (LogAbs.mk A'.m X.A.hi X.A.staged A'.ci) (s.log ++ ents.drop j) X.lo :=
      (logOk_m (X.A.store (prev + k + 1) (ents.drop k)) _ _ _ (by rw [hm]; rfl)).2 hlog
    have hpmm : prevMatch (s.log ++ ents.drop j) prev pt ∧
        matchedUpTo (s.log ++ ents.drop j) prev ents ents.length := by
      rcases hcase with ⟨hjl, hlen⟩ | ⟨hj, hlen⟩
      · exact crash_matched_store s.log prev pt ents j hpm hmu hlen (by omega)
      · subst hj; rw [List.drop_length, List.append_nil]; exact ⟨hpm, hmu⟩
    obtain ⟨hpm', hmu'⟩ := hpmm
    ihave Hol : |={E}=> (srvOwn γ i { s with log := s.log ++ ents.drop j } ∗
        logCouple γ i (s.log ++ ents.drop j)) $$ [Ho Hlc]
    · rcases hcase with ⟨hjl, hlen⟩ | ⟨hj, hlen⟩
      · iapply (gprot.followerStore_upd γ _ hE i s prev pt ents lci j ⟨hpm, hmu, hjl, hlen⟩)
        iframe; iframe #
      · subst hj
        rw [List.drop_length, List.append_nil, show ({ s with log := s.log } : SState) = s from rfl]
        imodintro; iframe
    imod Hol with ⟨Ho, Hlc⟩
    rcases lc with _ | v
    · imodintro
      iexists ({ X with s := { s with log := s.log ++ ents.drop j }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', tp := none })
      iunfold deadCore
      dsimp only
      try rw [hdp]
      rw [hD']
      simp only [tpRes, dpRes]
      iframe
      ipureintro
      refine ⟨⟨hlog', hlc, hvm, htd, ?_, by simpa using And.intro (q2_step X.lo X.lat X.pend none s.log (s.log ++ ents.drop j) s.dur.1 (s.dur.1) (Nat.le_refl _) (fun x st _ h => prevMatch_append _ _ _ _ h) hgrp.1) hgrp.2⟩, by simp, by simp, by simp, by simp⟩
      · rw [hc, hg]; exact hwp.1 rfl
    · obtain ⟨hv1, hv2⟩ := hlcv v rfl
      imod (gprot.learnCommitFollower γ _ hE i { s with log := s.log ++ ents.drop j } prev pt ents lci v
        ⟨hpm', hmu', hv1, hv2⟩) $$ [HI Ho Hdv Hae] with ⟨%d, Ho, Hdv, -, %hd⟩
      · iframe #; try iframe
      dsimp only at hd
      imodintro
      iexists ({ X with s := { s with log := s.log ++ ents.drop j, dur := d }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', tp := none })
      iunfold deadCore
      dsimp only
      try rw [hdp]
      rw [hD']
      simp only [tpRes, dpRes]
      iframe
      ipureintro
      refine ⟨⟨hlog', hlc, hvm, htd, ?_, by simpa using And.intro (q2_step X.lo X.lat X.pend none s.log (s.log ++ ents.drop j) s.dur.1 (d.1) (by omega) (fun x st _ h => prevMatch_append _ _ _ _ h) hgrp.1) hgrp.2⟩, by simp, by simp, by simp, by simp⟩
      · rw [hc, hg]; have := hwp.2 v rfl; omega
  | discard d =>
    simp only [pendDp] at hdp
    obtain ⟨hm, hc, hD'⟩ := hst
    iunfold pendHyps at Hh
    icases Hh with ⟨#Hae, #Hl⟩
    rw [hdp] at hgrp ⊢
    obtain ⟨⟨hdl, hpd, hll⟩, hcd, hq5a, hq5b⟩ := hgrp
    obtain ⟨m, b, hlat, hmi, hmt⟩ := hq5b d rfl
    imod (gprot.srvOwn_durLb γ _ hE i s) $$ [HI Ho] with ⟨Ho, #Hdl0⟩
    · iframe #; try iframe
    imod (gprot.installDiscard_upd γ _ hE i s d.x d.st d.ℓ hpre.1 hpre.2.1 hpre.2.2) $$ [HI Ho Hlc Hdv Hae Hl]
      with ⟨%L', %dd, Ho, Hlc, Hdv, #Hlbx, %hL, -⟩
    · iframe #; try iframe
    ihave %hmono := gprot.durView_lb γ i _ dd.1 s.dur.1 $$ [Hdv Hdl0]
    · iframe #; try iframe
    ihave Hnl : latestDur γ rc i X.lat none none $$ [Hlat]
    · unfold latestDur
      icases Hlat with ⟨Hlok, -⟩
      iframe Hlok
      dsimp only
      iright; iexists m, b
      isplitl []
      · ipureintro; exact hlat
      ileft; rw [hmi]; iframe Hlbx; ipureintro; rfl
    imodintro
    iexists ({ X with s := { s with log := L', dur := dd }, A := LogAbs.mk A'.m X.A.hi X.A.staged A'.ci, D := D', lo := d.x + 1, c := d.x, pend := none, dp := none, tp := none })
    iunfold deadCore
    dsimp only
    rw [hD']
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    refine ⟨⟨?_, by omega, hvm, htd, by rw [hc]; exact Nat.le_trans hci hmono,
      ⟨⟨fun d' h => (by cases h), fun x st id h => (by cases h), ?_⟩, fun d' h => (by cases h), by simp,
        fun d' h => (by cases h)⟩⟩, by simp, by simp, by simp, by simp⟩
    · unfold logOk
      rw [hm]
      constructor
      · intro k e h; simp at h
      · intro k h1 h2; omega
    · rw [hlat]; simp only [latIdxD]; omega

/-- (R2) No window survived: the dead state as is. -/
theorem srvDead_deadCore (X : SrvDur) : srvDead γ rc i X ⊢ deadCore γ rc i X := by
  unfold srvDead
  iintro ⟨H, -, -⟩
  iexact H

/-- (R2) **The next generation's vacant state**, from the dead state and the store authorities of
the next generation's handles `rc'` at the surviving image (the same entries and written commit
index; the staged index durable, `0` after a reopen): the pending term step fired
(`setTerm_upd`/`electTerm_upd` from `tpRes`), the pending install record dropped (its `snapFollow`
kept), and the commit index reset (`setCidx_upd … 0`, the atomic being volatile). A pending discard
is kept (`dp`, for `NewRaft`'s fix 2), unless the term step changed the term (then dropped). -/
theorem dead_vacant {E : CoPset} (hE : ↑gprotN ⊆ E)
    (rc' : RCtx GF) (X : SrvDur) (A' : LogAbs) (D' : StableAbs) (lat' : SnapLatest)
    (h : A'.m = X.A.m ∧ A'.ci = X.A.ci ∧ uint.nat A'.staged ≤ X.s.dur.1 ∧ D' = X.D ∧
      lat' = X.lat ∧ rc'.snapP = rc.snapP) :
    Inv γ ∗ deadCore γ rc i X ∗ rc'.ownL A' ∗ rc'.ownS D' ∗ rc'.ownSS lat' ⊢ |={E}=>
      ∃ X' : SrvDur, srvVacant γ rc' i X' ∗
        ⌜X'.s.cidx = 0 ∧ X'.tp = none ∧ X'.A = A' ∧ X'.D = D' ∧ X'.lat = lat' ∧
          X'.s.log = X.s.log ∧ X'.s.dur = X.s.dur⌝ := by
  obtain ⟨hAm, hAci, hstg, hD', hlat', hsnap⟩ := h
  iintro ⟨#HI, Hc, HL, HS, HSS⟩
  iunfold deadCore at Hc
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, %Hp, Hlat, Htp, Hdp⟩
  obtain ⟨hlo, hlc, hvm, htd, hci, ⟨⟨hdl, hpd, hll⟩, hcd, hq5a, hq5b⟩⟩ := Hp
  imod (gprot.srvOwn_durLb γ _ hE i X.s) $$ [HI Ho] with ⟨Ho, #Hdd⟩
  · iframe #; try iframe
  -- the pending term step
  ihave Hs1 : |={E}=> ∃ s1 : SState, srvOwn γ i s1 ∗ termCouple γ i s1.term ∗
      ⌜s1.log = X.s.log ∧ s1.dur = X.s.dur ∧ s1.cidx = X.s.cidx ∧ s1.vterm = X.s.vterm ∧
        s1.vcand = X.s.vcand ∧ X.s.term ≤ s1.term ∧ termDurOk X.D s1 none ∧
        (X.dp ≠ none → s1.term = X.s.term)⌝ $$ [Ho Htc Htp]
  · rcases htpX : X.tp with _ | (t | _)
    · try rw [htpX] at htd
      imodintro
      iexists X.s
      iframe
      ipureintro
      exact ⟨rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, htd, fun _ => rfl⟩
    · try rw [htpX] at htd
      try rw [htpX] at hq5a
      try rw [htpX]
      unfold termDurOk at htd
      rcases htd with ⟨h1, _⟩ | ⟨t', h1, h2, h3⟩ | ⟨h1, _⟩
      · cases h1
      · have ht : t = t' := TermPend.set.inj (Option.some.inj h1)
        subst ht
        iunfold tpRes at Htp
        imod (gprot.setTerm_upd γ _ hE i X.s t h3) $$ [HI Ho Htc Htp] with ⟨Ho, Htc, -⟩
        · iframe #; try iframe
        imodintro
        iexists { X.s with term := t }
        iframe
        ipureintro
        refine ⟨rfl, rfl, rfl, rfl, rfl, h3, Or.inl ⟨rfl, h2⟩, fun hne => ?_⟩
        rcases hq5a with h | h
        · cases h
        · exact absurd h hne
      · cases h1
    · try rw [htpX] at htd
      try rw [htpX] at hq5a
      try rw [htpX]
      unfold termDurOk at htd
      rcases htd with ⟨h1, _⟩ | ⟨t', h1, h2, h3⟩ | ⟨h1, h2⟩
      · cases h1
      · cases h1
      · iunfold tpRes at Htp
        imod (gprot.electTerm_upd γ _ hE i X.s) $$ [HI Ho Htc Htp] with ⟨Ho, Htc, -, -, -, -, -⟩
        · iframe #; try iframe
        imodintro
        iexists { X.s with term := X.s.term + 1 }
        iframe
        ipureintro
        refine ⟨rfl, rfl, rfl, rfl, rfl, by simp only; omega, Or.inl ⟨rfl, h2⟩, fun hne => ?_⟩
        rcases hq5a with h | h
        · cases h
        · exact absurd h hne
  imod Hs1 with ⟨%s1, Ho, Htc, %hs1⟩
  obtain ⟨hl1, hd1, hc1, hv1, hvc1, hle1, htd1, hdp1⟩ := hs1
  -- the commit index reset (the atomic is volatile)
  rw [← hc1]
  imod (gprot.setCidx_upd γ _ hE i s1 0 (Nat.zero_le _)) $$ [HI Ho Hcc] with ⟨Ho, Hcc⟩
  · iframe #; try iframe
  -- the snapshot store's part, without the dead generation's `lastApplied`
  ihave Hlv : latestDurV γ rc' i lat' X.dp $$ [Hlat]
  · unfold latestDur latestDurV
    rw [hlat', latestOk_snapP γ rc rc' X.lat hsnap]
    icases Hlat with ⟨Hlok, Hbr⟩
    iframe Hlok
    rcases hpX : X.pend with _ | ⟨x, st, id⟩
    · try rw [hpX]
      icases Hbr with (%hn | ⟨%m, %b, %hl, (⟨#Hdl, %hdn⟩ | ⟨#Hsf, %hdpd, -⟩)⟩)
      · ileft; ipureintro; exact hn
      · iright; iexists m, b; isplitl []; · ipureintro; exact hl
        ileft; iframe Hdl; ipureintro; exact hdn
      · iright; iexists m, b; isplitl []; · ipureintro; exact hl
        iright; iframe Hsf; ipureintro; exact hdpd
    · try rw [hpX]
      icases Hbr with ⟨%m, %b, %a, %hl, #Hsf, -⟩
      obtain ⟨hl1, hid, hx, hst, -⟩ := hl
      iright; iexists m, b; isplitl []; · ipureintro; exact hl1
      rcases hpd x st id hpX with ⟨ℓ, hℓ⟩ | ⟨hpm, hxd⟩
      · iright
        rw [hx, hst]
        iframe Hsf
        ipureintro
        exact ⟨ℓ, by rw [hℓ]⟩
      · rcases hdpX : X.dp with _ | d'
        · ileft
          rw [hx]
          ihave #Hx := gprot.durLb_mono γ i _ x hxd $$ Hdd
          iframe Hx
          ipureintro; rfl
        · obtain ⟨m', b', hl', hm1, hm2⟩ := hq5b d' hdpX
          have hl2 := hl1.symm.trans hl'
          simp only [Option.some.injEq, Prod.mk.injEq] at hl2
          obtain ⟨rfl, rfl⟩ := hl2
          iright
          rw [hx, hst]
          iframe Hsf
          ipureintro
          refine ⟨d'.ℓ, ?_⟩
          rcases d' with ⟨dx, dst, dl⟩
          simp only at hm1 hm2 ⊢
          rw [← hm1, ← hm2, hx, hst]
  ihave Hdp' : dpRes γ i { s1 with cidx := 0 } X.dp $$ [Hdp]
  · rcases hdpX : X.dp with _ | d
    · simp only [dpRes]; itrivial
    · try rw [hdpX]
      have ht1 : s1.term = X.s.term := hdp1 (by rw [hdpX]; simp)
      unfold dpRes
      dsimp only
      rw [ht1, hl1]
      iexact Hdp
  ihave Htp' : tpRes γ (none : Option TermPend) $$ []
  · simp only [tpRes]; itrivial
  imodintro
  iexists ({ X with s := { s1 with cidx := 0 }, A := A', D := D', lat := lat', pend := none, tp := none })
  unfold srvVacant
  dsimp only
  rw [hd1, hl1]
  iframe
  ipureintro
  refine ⟨⟨(logOk_m X.A A' _ _ hAm).2 hlo, hlc, ?_, ?_, by rw [hAci]; exact hci,
    hstg, rfl, ⟨⟨hdl, fun x st id h => (by cases h), by rw [hlat']; exact hll⟩, hcd,
      Or.inl rfl, by rw [hlat']; exact hq5b⟩⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [hD']
    unfold voteMatches at hvm ⊢
    obtain ⟨h1, h2⟩ := hvm
    refine ⟨by rw [hv1]; exact h1, ?_⟩
    rcases h2 with h | h | h
    · exact Or.inl (by rw [hv1]; exact h)
    · exact Or.inr (Or.inl (by simp only; rw [hv1]; omega))
    · exact Or.inr (Or.inr (by rw [hvc1]; exact h))
  · rw [hD']
    unfold termDurOk at htd1 ⊢
    exact htd1

end dead

end crashLaws

end github_com.hashicorp.raft

end Perennial
