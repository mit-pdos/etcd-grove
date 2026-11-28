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

theorem durStores_with (X : SrvDur) (s : SState) (tp : Option TermPend) (dp : Option DiscPend) :
    durStores γ rc i { X with s := s, tp := tp, dp := dp } = durStores γ rc i X := rfl

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
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp⟩
  rw [hs, htp, hdp] at *
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  imod Hf $$ Ho Hdv HP with ⟨%d, Ho, Hdv, %hle, HQ⟩
  unfold srvVP
  imod (ghostVar_update_halves ({ s with dur := d }, tp, dp) rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  rw [← dpRes_dur γ i s d dp]
  rw [← durStores_with γ rc i X { s with dur := d } tp dp]
  imod Hcl $$ %({ X with s := { s with dur := d }, tp := tp, dp := dp }) [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp] Hs with -
  · iunfold durCore
    dsimp only
    iframe
    ipureintro
    exact ⟨hlo, hlc, hvm, htd, by omega⟩
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
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp⟩
  rw [hs, htp, hdp] at *
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
  rw [← durStores_with γ rc i X { s with term := t } none none]
  imod Hcl $$ %({ X with s := { s with term := t }, tp := none, dp := none }) [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend] Hs with -
  · iunfold durCore
    dsimp only
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨hlo, hlc, ?_, ?_, hci⟩
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
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp⟩
  rw [hs, htp, hdp] at *
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
  rw [← durStores_with γ rc i X { s with term := s.term + 1 } none none]
  imod Hcl $$ %({ X with s := { s with term := s.term + 1 }, tp := none, dp := none }) [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend] Hs with -
  · iunfold durCore
    dsimp only
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    refine ⟨hlo, hlc, ?_, ?_, hci⟩
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
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp⟩
  rw [hs, htp, hdp] at *
  obtain ⟨hlo, hlc, hvm, htd, hci⟩ := Hp
  imod (gprot.setCidx_upd γ _ (crash_hE_gprot hE) i s c hc) $$ [HI Ho Hcc] with ⟨Ho, Hcc⟩
  · iframe #; try iframe
  unfold srvV cidxV
  imod (ghostVar_update_halves ({ s with cidx := c }, (none : Option TermPend), (none : Option DiscPend))
    rc.dur.sv _ _) $$ Hsv Hv with ⟨Hsv, Hv⟩
  imod (ghostVar_update_halves c rc.dur.cv _ _) $$ Hcv Ht with ⟨Hcv, Ht⟩
  rw [← durStores_with γ rc i X { s with cidx := c } none none]
  imod Hcl $$ %({ X with s := { s with cidx := c }, tp := none, dp := none }) [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp] Hs with -
  · iunfold durCore
    dsimp only
    simp only [tpRes, dpRes]
    iframe
    ipureintro
    try simp only [and_true]
    exact ⟨hlo, hlc, hvm, htd, hci⟩
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
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp⟩
  rw [Hat]
  ihave ⟨Htc, #Hlb⟩ := gprot.termCouple_get_lb γ i t $$ Htc
  imod Hcl $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp] Hs with -
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
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp⟩
  rw [Hat]
  ihave %hle := gprot.termCouple_lb γ i t t' $$ [Htc Hlb]
  · iframe #; try iframe
  imod Hcl $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp] Hs with -
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
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp⟩
  rw [Hat]
  imod (gprot.termCouple_now γ _ (crash_hE_gprot hE) i t s0) $$ [HI Hsrv Htc Hh] with ⟨Htc, HQ⟩
  · iframe #; try iframe
  imod Hcl $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp] Hs with -
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
  icases Hc with ⟨Ho, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hp, Hcomp, Hpend, Htp, Hdp⟩
  rw [Hat]
  imod (gprot.readCidx_repl γ _ (crash_hE_gprot hE) i T c) $$ [HI Hcc Hl Hlb] with ⟨Hcc, HQ⟩
  · iframe #; try iframe
  imod Hcl $$ %X [Ho Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpend Htp Hdp] Hs with -
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
  sorry -- hraft_robust R2: proof pending

/-- (R2) The stored entries are the protocol log's (from `logOk`). -/
theorem durCore_logOk (X : SrvDur) :
    durCore γ rc i X ⊢ durCore γ rc i X ∗
      ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ uint.nat X.A.ci ≤ X.s.dur.1⌝ := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) The protocol facts of the core's state (`srvOwn_facts` on it). -/
theorem durCore_facts (X : SrvDur) :
    Inv γ ∗ durCore γ rc i X ⊢ |={E}=> durCore γ rc i X ∗
      ⌜X.s.dur.1 ≤ X.s.log.length ∧ X.s.cidx ≤ X.s.dur.1 ∧ X.s.vterm ≤ X.s.term ∧
        X.s.log.length < 2 ^ 62⌝ := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) The installed snapshot's discard on the opened core (`installDiscard_upd`, R4b/R5's
`DeleteRange` with `Pend.discard`): the new log and durable prefix, the main goroutine's view (lent
in the window) and the pending discard cleared; the store coupling is the caller's (the delete's
range covers every stored entry; the frontier raised to `x`). -/
theorem installDiscard_core (X : SrvDur) (s : SState) (d : DiscPend) (A' : LogAbs) (c' : Nat)
    (hd : X.s = s ∧ X.dp = some d)
    (hA : (∀ k e, A'.m.lookup k = some e → d.x < k) ∧ A'.staged = X.A.staged ∧ A'.ci = X.A.ci)
    (hc : d.x ≤ c') :
    Inv γ ∗ durCore γ rc i X ∗ srvVP rc s X.tp (some d) ∗ compLb rc c' ⊢ |={E}=>
      ∃ (X' : SrvDur), durCore γ rc i X' ∗ srvVP rc X'.s X.tp none ∗ durLb γ i d.x ∗
        ([∗list] k ↦ e ∈ X'.s.log, CIdx γ (k + 1) e) ∗
        ⌜X'.A = A' ∧ X'.D = X.D ∧ X'.lat = X.lat ∧ X'.pend = X.pend ∧ X'.dp = none ∧
          X'.s.log.length = d.x ∧ lastTerm X'.s.log = d.st ∧ X'.s.dur.1 = d.x ∧
          X'.s.term = s.term ∧ X'.s.vterm = s.vterm ∧ X'.s.vcand = s.vcand ∧ X'.s.cidx = s.cidx⌝ := by
  sorry -- hraft_robust R2: proof pending

end core

/-! ## Generic atomic updates of the stores

Each builds the store's (crash-token) atomic update from `srvDurInv`: it opens the invariant (its
core without a later), hands the store's authority over, and at the commit (`f`'s new state) runs
the caller's step on the core, which must re-establish it with the other stores unchanged. -/

section stores

/-- (R2) A log-store write (`StoreLogs`, `StoreLog`, `StageCommitIndex`: `f` the write's effect). -/
theorem logWrite_au (f : LogAbs → LogAbs) (R Ψ : IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> ∃ X' : SrvDur, durCore γ rc i X' ∗
        ⌜X'.A = f X.A ∧ X'.D = X.D ∧ X'.lat = X.lat ∧ X'.pend = X.pend⌝ ∗ Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs, rc.ownL A ∗ (rc.ownL (f A) ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) A log-store `DeleteRange(mn, mx)` (the store chooses the new `hi'`). -/
theorem logDelete_au (mn mx : Nat) (R Ψ : IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ (X : SrvDur) (hi' : w64), durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> ∃ X' : SrvDur,
        durCore γ rc i X' ∗
        ⌜X'.A = X.A.delete mn mx hi' ∧ X'.D = X.D ∧ X'.lat = X.lat ∧ X'.pend = X.pend⌝ ∗ Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs, rc.ownL A ∗
        (∀ hi' : w64, rc.ownL (A.delete mn mx hi') ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) A log-store read (`GetLog`, `LastIndex`, `GetCommitIndex`): the caller's result over the
opened core (the store's state `X.A`, its coupling with `X.s`). -/
theorem logRead_au (R : IProp GF) (Ψ : LogAbs → IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> durCore γ rc i X ∗ Ψ X.A) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs, rc.ownL A ∗ (rc.ownL A ={∅, ⊤ \ ↑storeN}=∗ Ψ A) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) A stable-store write (`f` the write's effect). -/
theorem stableWrite_au (f : StableAbs → StableAbs) (R Ψ : IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> ∃ X' : SrvDur, durCore γ rc i X' ∗
        ⌜X'.D = f X.D ∧ X'.A = X.A ∧ X'.lat = X.lat ∧ X'.pend = X.pend⌝ ∗ Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D : StableAbs, rc.ownS D ∗ (rc.ownS (f D) ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) A stable-store read. -/
theorem stableRead_au (R : IProp GF) (Ψ : StableAbs → IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ R -∗ |={(⊤ \ ↑storeN) \ ↑durN}=> durCore γ rc i X ∗ Ψ X.D) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D : StableAbs, rc.ownS D ∗ (rc.ownS D ={∅, ⊤ \ ↑storeN}=∗ Ψ D) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) A snapshot-store commit (a sink's `Close`: `f` the store's new latest); the caller's step
also gets `latestDur` (under its later: it mentions `snapP`) and re-establishes it. -/
theorem snapWrite_au (f : SnapLatest → SnapLatest) (R Ψ : IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ ▷ latestDur γ rc i X.lat X.pend -∗ R -∗
        |={(⊤ \ ↑storeN) \ ↑durN}=> ∃ X' : SrvDur, durCore γ rc i X' ∗ ▷ latestDur γ rc i X'.lat X'.pend ∗
          ⌜X'.lat = f X.lat ∧ X'.A = X.A ∧ X'.D = X.D⌝ ∗ Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old : SnapLatest, rc.ownSS old ∗ (rc.ownSS (f old) ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) A snapshot-store read (`List`, `Open`). -/
theorem snapRead_au (R : IProp GF) (Ψ : SnapLatest → IProp GF) :
    srvDurInv γ rc i -∗ R -∗
      (∀ X : SrvDur, durCore γ rc i X -∗ ▷ latestDur γ rc i X.lat X.pend -∗ R -∗
        |={(⊤ \ ↑storeN) \ ↑durN}=> durCore γ rc i X ∗ ▷ latestDur γ rc i X.lat X.pend ∗ Ψ X.lat) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old : SnapLatest, rc.ownSS old ∗ (rc.ownSS old ={∅, ⊤ \ ↑storeN}=∗ Ψ old) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) `StageCommitIndex(idx)` by the main goroutine (its view of the staged index updated; no
window: volatile). -/
theorem stageCommit_au (D : StableAbs) (g idx : w64) (Ψ : IProp GF) :
    srvDurInv γ rc i -∗ stVS rc D g -∗ (stVS rc D idx ={⊤ \ ↑storeN}=∗ Ψ) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs, rc.ownL A ∗ (rc.ownL { A with staged := idx } ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  sorry -- hraft_robust R2: proof pending

end stores

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
    Inv γ -∗ srvDurInv γ rc i -∗ srvV rc s -∗ stVS rc D g -∗ pendHyps γ i s (.app es) -∗
      (srvV rc { s with log := s.log ++ es } -∗ stVS rc D g -∗
        ([∗list] k ↦ e ∈ es, llogIdx γ s.term (s.log.length + 1 + k) e) ={⊤ \ ↑storeN}=∗ Ψ) -∗
      logWin γ rc i (.store (s.log.length + 1) es) ∗
      (logWin γ rc i (.store (s.log.length + 1) es) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (rc.ownL (A.store (s.log.length + 1) es) ={∅, ⊤ \ ↑storeN}=∗ Ψ)) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) **The leader's configuration entry** at `StoreLogs`' commit (`leaderAppendCfg_upd`). -/
theorem storeLogs_cfg_win (s : SState) (e : Entry) (k p : Nat) (D : StableAbs) (g : w64)
    (hpre : pendPre γ i s (.cfg e k p)) (hg : uint.nat g ≤ s.dur.1) (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ srvV rc s -∗ stVS rc D g -∗ pendHyps γ i s (.cfg e k p) -∗
      (srvV rc { s with log := s.log ++ [e] } -∗ stVS rc D g -∗
        ccfgOwn γ i s.term (lastCfgIdx s.log) -∗
        llogIdx γ s.term (s.log.length + 1) e ={⊤ \ ↑storeN}=∗ Ψ) -∗
      logWin γ rc i (.store (s.log.length + 1) [e]) ∗
      (logWin γ rc i (.store (s.log.length + 1) [e]) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (rc.ownL (A.store (s.log.length + 1) [e]) ={∅, ⊤ \ ↑storeN}=∗ Ψ)) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) **The follower's append** at `StoreLogs`' commit (`followerStore_upd`), then, with
`lc = some v`, the commit learnt with it (`learnCommitFollower` of `min lci v`, so that the written
staged index `g ≤ min lci v` is durable). -/
theorem storeLogs_fstore_win (s : SState) (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (lc : Option Nat) (D : StableAbs) (g : w64)
    (hpre : pendPre γ i s (.fstore prev pt ents lci j lc))
    (hg : (lc = none → uint.nat g ≤ s.dur.1) ∧ (∀ v, lc = some v → uint.nat g ≤ Min.min lci v))
    (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ srvV rc s -∗ stVS rc D g -∗
      pendHyps γ i s (.fstore prev pt ents lci j lc) -∗
      (∀ d : Nat × Nat, srvV rc { s with log := s.log ++ ents.drop j, dur := d } -∗ stVS rc D g -∗
        ⌜s.dur.1 ≤ d.1 ∧ uint.nat g ≤ d.1 ∧
          (∀ v, lc = some v → d.1 = Max.max s.dur.1 (Min.min lci v)) ∧ (lc = none → d = s.dur)⌝ -∗
        (match lc with | none => iprop(True) | some v => durLb γ i (Min.min lci v)) ={⊤ \ ↑storeN}=∗ Ψ) -∗
      logWin γ rc i (.store (prev + j + 1) (ents.drop j)) ∗
      (logWin γ rc i (.store (prev + j + 1) (ents.drop j)) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (rc.ownL (A.store (prev + j + 1) (ents.drop j)) ={∅, ⊤ \ ↑storeN}=∗ Ψ)) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) **The follower's truncation** at `DeleteRange(prev + 1 + j, |s.log|)`'s commit
(`truncate_upd`). -/
theorem deleteRange_trunc_win (s : SState) (prev pt : Nat) (ents : RLog) (lci j : Nat)
    (hpre : pendPre γ i s (.trunc prev pt ents lci j)) (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ srvV rc s -∗ pendHyps γ i s (.trunc prev pt ents lci j) -∗
      (srvV rc { s with log := s.log.take (prev + j) } -∗ ⌜s.dur.1 < prev + 1 + j⌝ ={⊤ \ ↑storeN}=∗ Ψ) -∗
      ∀ (D : StableAbs) (g : w64), stVS rc D g -∗
      (logWin γ rc i (.del (prev + 1 + j) s.log.length) ∗
      (logWin γ rc i (.del (prev + 1 + j) s.log.length) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
        rc.ownL A ∗ (∀ hi' : w64, rc.ownL (A.delete (prev + 1 + j) s.log.length hi')
          ={∅, ⊤ \ ↑storeN}=∗ stVS rc D g -∗ Ψ))) := by
  sorry -- hraft_robust R2: proof pending

/-- (R2) **`SetUint64(CurrentTerm, t)`'s commit** (`setCurrentTerm`): no model step; the term step
recorded pending (`tp`, its `tpRes` moved into the crash state), fired at the atomic store
(`setTerm_R`/`electTerm_R`). `tv` the written value: `t` (`.set t`) or `s.term + 1` (`.elect`). -/
theorem setUint64_term_win (s : SState) (tp : TermPend) (tv : Nat) (D : StableAbs) (g : w64)
    (ht : (tp = .set tv ∧ s.term ≤ tv) ∨ (tp = .elect ∧ tv = s.term + 1)) (h64 : tv < 2 ^ 64)
    (Ψ : IProp GF) :
    srvDurInv γ rc i -∗ srvV rc s -∗ stVS rc D g -∗ tpRes γ (some tp) -∗
      (srvVP rc s (some tp) none -∗
        stVS rc { D with ints := D.ints.insert (go!"CurrentTerm" : List w8) (W64 tv) } g
          ={⊤ \ ↑storeN}=∗ Ψ) -∗
      stWin γ rc i (.setU (go!"CurrentTerm" : List w8) (W64 tv)) ∗
      (stWin γ rc i (.setU (go!"CurrentTerm" : List w8) (W64 tv)) -∗
        |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D0 : StableAbs, rc.ownS D0 ∗
          (rc.ownS { D0 with ints := D0.ints.insert (go!"CurrentTerm" : List w8) (W64 tv) }
            ={∅, ⊤ \ ↑storeN}=∗ Ψ)) := by
  sorry -- hraft_robust R2: proof pending

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
  sorry -- hraft_robust R2: proof pending

/-- (R2) **`SetUint64(LastVoteTerm, s.term)`'s commit** (`persistVote`'s second write): the vote
(`grantVote_upd`), `LastVoteCand = c` already stored. -/
theorem setUint64_vote_win (s : SState) (c : SID) (li lt : Nat) (D : StableAbs) (g : w64)
    (hpre : pendPre γ i s (.vote c li lt))
    (hc : D.bytes.lookup (go!"LastVoteCand" : List w8) = some c) (Ψ : IProp GF) :
    Inv γ -∗ srvDurInv γ rc i -∗ srvV rc s -∗ stVS rc D g -∗ candIs γ c s.term li lt -∗
      (srvV rc { s with vterm := s.term, vcand := c } -∗
        stVS rc { D with ints := D.ints.insert (go!"LastVoteTerm" : List w8) (W64 s.term) } g -∗
        voteIs γ i s.term c ={⊤ \ ↑storeN}=∗ Ψ) -∗
      stWin γ rc i (.setU (go!"LastVoteTerm" : List w8) (W64 s.term)) ∗
      (stWin γ rc i (.setU (go!"LastVoteTerm" : List w8) (W64 s.term)) -∗
        |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ D0 : StableAbs, rc.ownS D0 ∗
          (rc.ownS { D0 with ints := D0.ints.insert (go!"LastVoteTerm" : List w8) (W64 s.term) }
            ={∅, ⊤ \ ↑storeN}=∗ Ψ)) := by
  sorry -- hraft_robust R2: proof pending

end commits

end crashLaws

end github_com.hashicorp.raft

end Perennial
