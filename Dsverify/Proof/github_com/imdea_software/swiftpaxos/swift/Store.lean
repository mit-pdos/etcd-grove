/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Store.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The returned-rows store's operations** (round 34, sv-swb; notes/lifecycle-plan.md R.2/R5.2,
notes/lifecycle-table.md revision 5/5b/6 §3.4 T7, T11₀, T16a, T19, T23, T24, §3.7, §3.10): they
open the node invariant (`nodeInvD`'s store, DescNode.lean) and the epoch's descriptors' invariant
(`descInv`'s ledger half, DescState.lean).

* `swift.store_take`: a claim's token out of the store (record `recOf ck`), the key into the
  ledger `Out` with the taker's registry share `γn j ↦{qj} false` as its body, the receipt
  `outRcpt K (j, qj)` to the taker. The taker's loan token refutes a stopped epoch.
* `swift.store_put`: a token back into the store with any record (T16a: `exec`), the key out of
  the ledger by its receipt, the registry share back.
* `swift.store_putR`: as `store_put`, with a new claim of kind `ck` on the record `recOf ck`
  (T19 and T7's end: `rest d γi`).
* `swift.store_release`: a `rest d γi` claim releases its record (T23): the record's contents
  back, the record `released`, the claim consumed.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.StopDescs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

theorem swift.nodeN_desc_sub : ↑swift.nodeN ⊆ (⊤ \ ↑swift.descN : CoPset) := by
  have h : ↑swift.nodeN ## (↑swift.descN : CoPset) := by
    unfold swift.nodeN swift.descN
    exact ndot_ne_disjoint nroot (by decide)
  intro e he
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => h e ⟨he, h'⟩⟩

/-! ## The store's pure invariant under the operations -/

section pure

theorem swift.storeOk_take (cb : Nat) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Out : GMap (Nat × sp.CmdId) (Nat × Qp))
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) (K : Nat × sp.CmdId) (ck : swift.ClK) (jq : Nat × Qp)
    (h : swift.storeOk cb O Rt Out Cl) (hc : Cl.lookup K = some ck) :
    swift.storeOk cb O (Rt.delete K) (Out.insert K jq) (Cl.delete K) ∧ Out.lookup K = none ∧
      Rt.lookup K = some (swift.recOf ck) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hR := h5 K ck hc
  have hO : Out.lookup K = none := h3 K (by simp [hR])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hO, hR⟩
  · intro K' hK'
    by_cases e : K = K'
    · subst e; exact h1 K (Or.inl (by simp [hR]))
    · rw [GMap.lookup_delete_iff, GMap.lookup_insert_eq_iff, if_neg e, if_neg e] at hK'
      exact h1 K' hK'
  · intro K' hc' hK'
    by_cases e : K = K'
    · subst e; right; rw [GMap.lookup_insert_eq_iff, if_pos rfl]; rfl
    · rw [GMap.lookup_delete_iff, GMap.lookup_insert_eq_iff, if_neg e, if_neg e]
      exact h2 K' hc' hK'
  · intro K' hK'
    by_cases e : K = K'
    · subst e; rw [GMap.lookup_delete_iff, if_pos rfl] at hK'; cases hK'
    · rw [GMap.lookup_delete_iff, if_neg e] at hK'
      rw [GMap.lookup_insert_eq_iff, if_neg e]; exact h3 K' hK'
  · intro K' hK'
    by_cases e : K = K'
    · subst e; exact h4 K (Or.inl (by simp [hR]))
    · rw [GMap.lookup_delete_iff, GMap.lookup_insert_eq_iff, if_neg e, if_neg e] at hK'
      exact h4 K' hK'
  · intro K' c' hc'
    by_cases e : K = K'
    · subst e; rw [GMap.lookup_delete_iff, if_pos rfl] at hc'; cases hc'
    · rw [GMap.lookup_delete_iff, if_neg e] at hc' ⊢; exact h5 K' c' hc'

theorem swift.storeOk_put (cb : Nat) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Out : GMap (Nat × sp.CmdId) (Nat × Qp))
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) (K : Nat × sp.CmdId) (rk : swift.RecK) (jq : Nat × Qp)
    (h : swift.storeOk cb O Rt Out Cl) (hO : Out.lookup K = some jq) :
    swift.storeOk cb O (Rt.insert K rk) (Out.delete K) Cl ∧ Rt.lookup K = none ∧
      Cl.lookup K = none := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hR : Rt.lookup K = none := by
    cases e : Rt.lookup K with
    | none => rfl
    | some v => have := h3 K (by simp [e]); rw [hO] at this; cases this
  have hC : Cl.lookup K = none := by
    cases e : Cl.lookup K with
    | none => rfl
    | some c => have := h5 K c e; rw [hR] at this; cases this
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hR, hC⟩
  · intro K' hK'
    by_cases e : K = K'
    · subst e; exact h1 K (Or.inr (by simp [hO]))
    · rw [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff, if_neg e, if_neg e] at hK'
      exact h1 K' hK'
  · intro K' hc' hK'
    by_cases e : K = K'
    · subst e; left; rw [GMap.lookup_insert_eq_iff, if_pos rfl]; rfl
    · rw [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff, if_neg e, if_neg e]
      exact h2 K' hc' hK'
  · intro K' _
    by_cases e : K = K'
    · subst e; rw [GMap.lookup_delete_iff, if_pos rfl]
    · rename_i hK'
      rw [GMap.lookup_insert_eq_iff, if_neg e] at hK'
      rw [GMap.lookup_delete_iff, if_neg e]; exact h3 K' hK'
  · intro K' hK'
    by_cases e : K = K'
    · subst e; exact h4 K (Or.inr (by simp [hO]))
    · rw [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff, if_neg e, if_neg e] at hK'
      exact h4 K' hK'
  · intro K' c' hc'
    by_cases e : K = K'
    · subst e; rw [hC] at hc'; cases hc'
    · rw [GMap.lookup_insert_eq_iff, if_neg e]; exact h5 K' c' hc'

theorem swift.storeOk_putR (cb : Nat) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Out : GMap (Nat × sp.CmdId) (Nat × Qp))
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) (K : Nat × sp.CmdId) (ck : swift.ClK) (jq : Nat × Qp)
    (h : swift.storeOk cb O Rt Out Cl) (hO : Out.lookup K = some jq) :
    swift.storeOk cb O (Rt.insert K (swift.recOf ck)) (Out.delete K) (Cl.insert K ck) ∧
      Cl.lookup K = none := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, -, hC⟩ := swift.storeOk_put cb O Rt Out Cl K (swift.recOf ck) jq h hO
  refine ⟨⟨h1, h2, h3, h4, ?_⟩, hC⟩
  intro K' c' hc'
  by_cases e : K = K'
  · subst e; rw [GMap.lookup_insert_eq_iff, if_pos rfl] at hc'; cases hc'
    rw [GMap.lookup_insert_eq_iff, if_pos rfl]
  · rw [GMap.lookup_insert_eq_iff, if_neg e] at hc'; exact h5 K' c' hc'

theorem swift.storeOk_release (cb : Nat) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Out : GMap (Nat × sp.CmdId) (Nat × Qp))
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) (K : Nat × sp.CmdId)
    (h : swift.storeOk cb O Rt Out Cl) (hR : (Rt.lookup K).isSome) :
    swift.storeOk cb O (Rt.insert K .released) Out (Cl.delete K) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K' hK'
    by_cases e : K = K'
    · subst e; exact h1 K (Or.inl hR)
    · rw [GMap.lookup_insert_eq_iff, if_neg e] at hK'; exact h1 K' hK'
  · intro K' hc' hK'
    by_cases e : K = K'
    · subst e; left; rw [GMap.lookup_insert_eq_iff, if_pos rfl]; rfl
    · rw [GMap.lookup_insert_eq_iff, if_neg e]; exact h2 K' hc' hK'
  · intro K' hK'
    by_cases e : K = K'
    · subst e; exact h3 K hR
    · rw [GMap.lookup_insert_eq_iff, if_neg e] at hK'; exact h3 K' hK'
  · intro K' hK'
    by_cases e : K = K'
    · subst e; exact h4 K (Or.inl hR)
    · rw [GMap.lookup_insert_eq_iff, if_neg e] at hK'; exact h4 K' hK'
  · intro K' c' hc'
    by_cases e : K = K'
    · subst e; rw [GMap.lookup_delete_iff, if_pos rfl] at hc'; cases hc'
    · rw [GMap.lookup_delete_iff, if_neg e] at hc'
      rw [GMap.lookup_insert_eq_iff, if_neg e]; exact h5 K' c' hc'

end pure

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- The store's records' bodies (`storeD`'s big separating map). -/
abbrev swift.recBody (γ : sp.Names) (γo : GName) (sn : swift.StN) (K : Nat × sp.CmdId)
    (rk : swift.RecK) : IProp netDistGF :=
  iprop(∃ rv : swift.RowV, swift.rowTok γo K.1 K.2 rv ∗
    swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗ swift.tixOr sn.γxu sn.γxm K)

/-- **The take** (T11₀/T24 at the install step, T7's start; table rev 5/6): see the file
header. -/
theorem swift.store_take (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (γd γn : GName) (g : swift.DescG) (ep : swift.EpN) (DR : Loc → IProp netDistGF)
    (Run : Loc → swift.CommandId → IProp netDistGF) (str : swift.CommandId → GoString)
    (iL : Nat) (ql : Qp) (K : Nat × sp.CmdId) (ck : swift.ClK) (j : Nat) (qj : Qp) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      inv swift.descN (swift.descInv γ γd γn sn.γout g ep DR Run str) ∗
      swift.epochLoan g.γq iL ql ∗ ghostMapElem γn j (DFrac.own qj) false ∗
      swift.claimTok sn.γcl K ck ⊢
    |={⊤}=> ∃ rv : swift.RowV, swift.rowTok γo K.1 K.2 rv ∗
      swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv (swift.recOf ck) ∗
      swift.tixOr sn.γxu sn.γxm K ∗
      swift.epochLoan g.γq iL ql ∗ swift.outRcpt sn.γout K (j, qj) := by
  iintro ⟨#HN, #HD, Hloan, Hj, Hcl⟩
  iinv HD with Hd Hclose
  iunfold swift.descInv at Hd
  icases Hd with ⟨%st, >Hst, Hrest⟩
  cases st
  rotate_right
  · simp only [↓reduceIte]
    icases Hrest with >Ha
    iexfalso
    iapply swift.loan_not_stopped $$ [Ha Hloan]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  iunfold swift.ledgerD at Hled
  icases Hled with ⟨%Out, >HOa, >Hbod⟩
  imod (inv_acc (E := ⊤ \ ↑swift.descN) (N := swift.nodeN) swift.nodeN_desc_sub) $$ HN
    with ⟨Hn, Hclose2⟩
  iunfold swift.nodeInvD at Hn
  imod Hn
  icases Hn with ⟨%st, %O, Hstn, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out', %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  ihave %HeqO := ghostMapAuth_agree sn.γout _ _ Out Out' $$ HOa Ha
  subst HeqO
  iunfold swift.claimTok at Hcl
  ihave %Hl := ghost_map_lookup $$ Hc Hcl
  obtain ⟨h', hO, hR⟩ := swift.storeOk_take st.cballot O Rt Out Cl K ck (j, qj) h Hl
  icases (BigSepM.bigSepM_delete (show PartialMap.get? Rt K = some (swift.recOf ck) from hR)).1
    $$ Hm with ⟨⟨%rv, Htok, Hw, Htx⟩, Hm⟩
  imod ghost_map_delete $$ Hc Hcl with Hc
  ihave Hfull := (ghostMapAuth_halves sn.γout Out).2 $$ [HOa Ha]
  · iframe
  imod ghost_map_insert K (j, qj) hO $$ Hfull with ⟨Hfull, Hrc⟩
  icases (ghostMapAuth_halves sn.γout _).1 $$ Hfull with ⟨HOa, Ha⟩
  imod Hclose2 $$ [Hstn Hw2 He HO HX Ha Hc Hm Hu] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe Hstn Hw2 He HO HX
    isplitl [Ha Hc Hm Hu]
    · iunfold swift.storeD
      iexists Rt.delete K, Out.insert K (j, qj), Cl.delete K, U
      iframe Ha Hc Hm Hu
      ipureintro; exact ⟨h', hU⟩
    ipureintro; exact ⟨Hacc, Hok⟩
  imod Hclose $$ [Hst HW HWd Hview Hents HK Hpool Hrec HOa Hbod Hj Hrca] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst
    iexists Mc, q0, L, dm1, W
    iframe HW HWd Hview Hents HK Hpool Hrec Hrca
    iunfold swift.ledgerD
    iexists Out.insert K (j, qj)
    iframe HOa
    iapply (BigSepM.bigSepM_insert (Φ := fun (_ : Nat × sp.CmdId) (jq : Nat × Qp) =>
      ghostMapElem γn jq.1 (DFrac.own jq.2) false)
      (show Iris.Std.PartialMap.get? Out K = none from hO)).2
    iframe Hbod Hj
  imodintro
  iexists rv
  iframe Htok Hw Htx Hloan
  iunfold swift.outRcpt
  iexact Hrc

/-- **The deposit** (T16a with an `exec` record; any record `rk`): see the file header. -/
theorem swift.store_put (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (γd γn : GName) (g : swift.DescG) (ep : swift.EpN) (DR : Loc → IProp netDistGF)
    (Run : Loc → swift.CommandId → IProp netDistGF) (str : swift.CommandId → GoString)
    (iL : Nat) (ql : Qp) (K : Nat × sp.CmdId) (rk : swift.RecK) (rv : swift.RowV) (jq : Nat × Qp) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      inv swift.descN (swift.descInv γ γd γn sn.γout g ep DR Run str) ∗
      swift.epochLoan g.γq iL ql ∗ swift.rowTok γo K.1 K.2 rv ∗
      swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗ swift.tixOr sn.γxu sn.γxm K ∗
      swift.outRcpt sn.γout K jq ⊢
    |={⊤}=> swift.epochLoan g.γq iL ql ∗ ghostMapElem γn jq.1 (DFrac.own jq.2) false := by
  iintro ⟨#HN, #HD, Hloan, Htok, Hw, Htx, Hrc⟩
  iinv HD with Hd Hclose
  iunfold swift.descInv at Hd
  icases Hd with ⟨%st, >Hst, Hrest⟩
  cases st
  rotate_right
  · simp only [↓reduceIte]
    icases Hrest with >Ha
    iexfalso
    iapply swift.loan_not_stopped $$ [Ha Hloan]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  iunfold swift.ledgerD at Hled
  icases Hled with ⟨%Out, >HOa, >Hbod⟩
  imod (inv_acc (E := ⊤ \ ↑swift.descN) (N := swift.nodeN) swift.nodeN_desc_sub) $$ HN
    with ⟨Hn, Hclose2⟩
  iunfold swift.nodeInvD at Hn
  imod Hn
  icases Hn with ⟨%st, %O, Hstn, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out', %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  ihave %HeqO := ghostMapAuth_agree sn.γout _ _ Out Out' $$ HOa Ha
  subst HeqO
  iunfold swift.outRcpt at Hrc
  ihave %Hl := ghost_map_lookup $$ Ha Hrc
  obtain ⟨h', hR, -⟩ := swift.storeOk_put st.cballot O Rt Out Cl K rk jq h Hl
  icases (BigSepM.bigSepM_delete (show PartialMap.get? Out K = some jq from Hl)).1
    $$ Hbod with ⟨Hj, Hbod⟩
  ihave Hfull := (ghostMapAuth_halves sn.γout Out).2 $$ [HOa Ha]
  · iframe
  imod ghost_map_delete $$ Hfull Hrc with Hfull
  icases (ghostMapAuth_halves sn.γout _).1 $$ Hfull with ⟨HOa, Ha⟩
  imod Hclose2 $$ [Hstn Hw2 He HO HX Ha Hc Hm Hu Htok Hw Htx] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe Hstn Hw2 He HO HX
    isplitl [Ha Hc Hm Hu Htok Hw Htx]
    · iunfold swift.storeD
      iexists Rt.insert K rk, Out.delete K, Cl, U
      iframe Ha Hc Hu
      isplitl [Hm Htok Hw Htx]
      · iapply (BigSepM.bigSepM_insert (Φ := fun (K : Nat × sp.CmdId) (rk : swift.RecK) =>
          iprop(∃ rv : swift.RowV, swift.rowTok γo K.1 K.2 rv ∗
            swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗ swift.tixOr sn.γxu sn.γxm K))
          (show Iris.Std.PartialMap.get? Rt K = none from hR)).2
        iframe Hm
        iexists rv; iframe
      ipureintro; exact ⟨h', hU⟩
    ipureintro; exact ⟨Hacc, Hok⟩
  imod Hclose $$ [Hst HW HWd Hview Hents HK Hpool Hrec HOa Hbod Hrca] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst
    iexists Mc, q0, L, dm1, W
    iframe HW HWd Hview Hents HK Hpool Hrec Hrca
    iunfold swift.ledgerD
    iexists Out.delete K
    iframe HOa Hbod
  imodintro
  iframe Hloan Hj

/-- **The deposit with a new claim** (T19, T7's end: a `rest d γi` record; table rev 5 C2):
see the file header. -/
theorem swift.store_putR (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (γd γn : GName) (g : swift.DescG) (ep : swift.EpN) (DR : Loc → IProp netDistGF)
    (Run : Loc → swift.CommandId → IProp netDistGF) (str : swift.CommandId → GoString)
    (iL : Nat) (ql : Qp) (K : Nat × sp.CmdId) (ck : swift.ClK) (rv : swift.RowV) (jq : Nat × Qp) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      inv swift.descN (swift.descInv γ γd γn sn.γout g ep DR Run str) ∗
      swift.epochLoan g.γq iL ql ∗ swift.rowTok γo K.1 K.2 rv ∗
      swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv (swift.recOf ck) ∗ swift.tixOr sn.γxu sn.γxm K ∗
      swift.outRcpt sn.γout K jq ⊢
    |={⊤}=> swift.epochLoan g.γq iL ql ∗ ghostMapElem γn jq.1 (DFrac.own jq.2) false ∗
      swift.claimTok sn.γcl K ck := by
  iintro ⟨#HN, #HD, Hloan, Htok, Hw, Htx, Hrc⟩
  iinv HD with Hd Hclose
  iunfold swift.descInv at Hd
  icases Hd with ⟨%st, >Hst, Hrest⟩
  cases st
  rotate_right
  · simp only [↓reduceIte]
    icases Hrest with >Ha
    iexfalso
    iapply swift.loan_not_stopped $$ [Ha Hloan]
    iframe
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  iunfold swift.ledgerD at Hled
  icases Hled with ⟨%Out, >HOa, >Hbod⟩
  imod (inv_acc (E := ⊤ \ ↑swift.descN) (N := swift.nodeN) swift.nodeN_desc_sub) $$ HN
    with ⟨Hn, Hclose2⟩
  iunfold swift.nodeInvD at Hn
  imod Hn
  icases Hn with ⟨%st, %O, Hstn, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out', %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  ihave %HeqO := ghostMapAuth_agree sn.γout _ _ Out Out' $$ HOa Ha
  subst HeqO
  iunfold swift.outRcpt at Hrc
  ihave %Hl := ghost_map_lookup $$ Ha Hrc
  obtain ⟨h', hC⟩ := swift.storeOk_putR st.cballot O Rt Out Cl K ck jq h Hl
  have hR : Rt.lookup K = none := (swift.storeOk_put st.cballot O Rt Out Cl K (swift.recOf ck) jq h Hl).2.1
  icases (BigSepM.bigSepM_delete (show PartialMap.get? Out K = some jq from Hl)).1
    $$ Hbod with ⟨Hj, Hbod⟩
  ihave Hfull := (ghostMapAuth_halves sn.γout Out).2 $$ [HOa Ha]
  · iframe
  imod ghost_map_delete $$ Hfull Hrc with Hfull
  icases (ghostMapAuth_halves sn.γout _).1 $$ Hfull with ⟨HOa, Ha⟩
  imod ghost_map_insert K ck hC $$ Hc with ⟨Hc, Hcl⟩
  imod Hclose2 $$ [Hstn Hw2 He HO HX Ha Hc Hm Hu Htok Hw Htx] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe Hstn Hw2 He HO HX
    isplitl [Ha Hc Hm Hu Htok Hw Htx]
    · iunfold swift.storeD
      iexists Rt.insert K (swift.recOf ck), Out.delete K, Cl.insert K ck, U
      iframe Ha Hc Hu
      isplitl [Hm Htok Hw Htx]
      · iapply (BigSepM.bigSepM_insert (Φ := fun (K : Nat × sp.CmdId) (rk : swift.RecK) =>
          iprop(∃ rv : swift.RowV, swift.rowTok γo K.1 K.2 rv ∗
            swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗ swift.tixOr sn.γxu sn.γxm K))
          (show Iris.Std.PartialMap.get? Rt K = none from hR)).2
        iframe Hm
        iexists rv; iframe
      ipureintro; exact ⟨h', hU⟩
    ipureintro; exact ⟨Hacc, Hok⟩
  imod Hclose $$ [Hst HW HWd Hview Hents HK Hpool Hrec HOa Hbod Hrca] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst
    iexists Mc, q0, L, dm1, W
    iframe HW HWd Hview Hents HK Hpool Hrec Hrca
    iunfold swift.ledgerD
    iexists Out.delete K
    iframe HOa Hbod
  imodintro
  iframe Hloan Hj
  iunfold swift.claimTok
  iexact Hcl

/-- **A token put back with the ledger in hand** (round 40; table rev 10 T19h, §3R10.16 #6, plan
R10.3 `store_putRD`): `store_putR`'s core, for a caller already inside `descN`'s opening with
`ledgerD` in hand (T19h's single opening): only the node invariant is opened; the ledger's `Out K`
is deleted and its registry share comes back. -/
theorem swift.store_putRD (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (γn : GName) (K : Nat × sp.CmdId) (ck : swift.ClK) (rv : swift.RowV) (jq : Nat × Qp)
    (E : CoPset) (hE : ↑swift.nodeN ⊆ E) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ swift.ledgerD γn sn.γout ∗
      swift.rowTok γo K.1 K.2 rv ∗
      swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv (swift.recOf ck) ∗ swift.tixOr sn.γxu sn.γxm K ∗
      swift.outRcpt sn.γout K jq ⊢
    |={E}=> swift.ledgerD γn sn.γout ∗ ghostMapElem γn jq.1 (DFrac.own jq.2) false ∗
      swift.claimTok sn.γcl K ck := by
  iintro ⟨#HN, Hled, Htok, Hw, Htx, Hrc⟩
  iunfold swift.ledgerD at Hled
  icases Hled with ⟨%Out, HOa, Hbod⟩
  imod (inv_acc (E := E) (N := swift.nodeN) hE) $$ HN with ⟨Hn, Hclose2⟩
  iunfold swift.nodeInvD at Hn
  imod Hn
  icases Hn with ⟨%st, %O, Hstn, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out', %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  ihave %HeqO := ghostMapAuth_agree sn.γout _ _ Out Out' $$ HOa Ha
  subst HeqO
  iunfold swift.outRcpt at Hrc
  ihave %Hl := ghost_map_lookup $$ Ha Hrc
  obtain ⟨h', hC⟩ := swift.storeOk_putR st.cballot O Rt Out Cl K ck jq h Hl
  have hR : Rt.lookup K = none := (swift.storeOk_put st.cballot O Rt Out Cl K (swift.recOf ck) jq h Hl).2.1
  icases (BigSepM.bigSepM_delete (show PartialMap.get? Out K = some jq from Hl)).1
    $$ Hbod with ⟨Hj, Hbod⟩
  ihave Hfull := (ghostMapAuth_halves sn.γout Out).2 $$ [HOa Ha]
  · iframe
  imod ghost_map_delete $$ Hfull Hrc with Hfull
  icases (ghostMapAuth_halves sn.γout _).1 $$ Hfull with ⟨HOa, Ha⟩
  imod ghost_map_insert K ck hC $$ Hc with ⟨Hc, Hcl⟩
  imod Hclose2 $$ [Hstn Hw2 He HO HX Ha Hc Hm Hu Htok Hw Htx] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe Hstn Hw2 He HO HX
    isplitl [Ha Hc Hm Hu Htok Hw Htx]
    · iunfold swift.storeD
      iexists Rt.insert K (swift.recOf ck), Out.delete K, Cl.insert K ck, U
      iframe Ha Hc Hu
      isplitl [Hm Htok Hw Htx]
      · iapply (BigSepM.bigSepM_insert (Φ := fun (K : Nat × sp.CmdId) (rk : swift.RecK) =>
          iprop(∃ rv : swift.RowV, swift.rowTok γo K.1 K.2 rv ∗
            swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗ swift.tixOr sn.γxu sn.γxm K))
          (show Iris.Std.PartialMap.get? Rt K = none from hR)).2
        iframe Hm
        iexists rv; iframe
      ipureintro; exact ⟨h', hU⟩
    ipureintro; exact ⟨Hacc, Hok⟩
  imodintro
  iframe Hj
  isplitl [HOa Hbod]
  · iunfold swift.ledgerD
    iexists Out.delete K
    iframe HOa Hbod
  iunfold swift.claimTok
  iexact Hcl

theorem swift.retWhy_released (γ : sp.Names) (γxm γcg : GName) (str : swift.CommandId → GoString)
    (N r : Nat) (K : Nat × sp.CmdId) (rv : swift.RowV) :
    swift.freeSp γcg K.1 ⊢ (swift.retWhy γ γxm γcg str N r K rv .released : IProp netDistGF) := by
  simp only [swift.retWhy]; exact .rfl

/-- **A ballot's free permit spent** (round B1, D82 (4)): `(b, true) ↦ some _` in the epochs'
map, persisted (`handleSync`, before its free: `swift.descPoolCtxS`'s update). -/
theorem swift.freeP_spend (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat) (b : Nat) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ swift.freeP sn.γcg b ⊢
    |={⊤}=> swift.freeSp sn.γcg b := by
  iintro ⟨#HN, Hfp⟩
  iinv HN with Hn Hclose
  iunfold swift.nodeInvD at Hn
  imod Hn
  icases Hn with ⟨%st, %O, Hstn, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.nodeX at HX
  icases HX with ⟨HXT, HXs, HXb, HXcg⟩
  iunfold swift.cgAuth at HXcg
  icases HXcg with ⟨%G, HGa, %hG⟩
  iunfold swift.freeP at Hfp
  ihave %hGl := ghost_map_lookup $$ HGa Hfp
  imod ghost_map_update (γ := sn.γcg) (some sn.γcg : Option GName) $$ HGa Hfp with ⟨HGa, Hfp⟩
  imod (ghostMapElem_persist _ _ _ _) $$ Hfp with #Hfp
  imod Hclose $$ [Hstn Hw2 He HO HS HXT HXs HXb HGa] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe Hstn Hw2 He HO HS
    isplitl [HXT HXs HXb HGa]
    · iunfold swift.nodeX
      iframe HXT HXs HXb
      iunfold swift.cgAuth
      iexists G.insert (b, true) (some sn.γcg)
      iframe HGa
      ipureintro
      constructor
      · intro k' h
        rw [GMap.lookup_insert_eq_iff] at h
        by_cases e : (b, true) = k'
        · subst e; exact hG.1 _ (by rw [hGl]; rfl)
        · rw [if_neg e] at h; exact hG.1 k' h
      · intro b' h
        rw [GMap.lookup_insert_eq_iff, if_neg (by simp)]
        by_cases e : (b, true) = (b', true)
        · simp only [Prod.mk.injEq, and_true] at e; subst e
          exact hG.2 _ (by rw [hGl]; rfl)
        · rw [GMap.lookup_insert_eq_iff, if_neg e] at h; exact hG.2 b' h
    ipureintro; exact ⟨Hacc, Hok⟩
  imodintro
  iunfold swift.freeSp
  iexists sn.γcg
  iexact Hfp

/-- **A rest record released** (T23, table rev 5 C2/C5): the `rest d γi` claim consumes its
record's contents (the half fields, `γi`'s half, the snapshot); the record stays `released` (its
token in the store, for the report). Only the node invariant is opened. Round B1 (D82 (4)): with
the ballot's spent free permit, which the `released` record keeps (`retWhy .released`): the
report, holding the permit unspent, sees no `released` record of its ballot. -/
theorem swift.store_release (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (K : Nat × sp.CmdId) (d : Loc) (γi : GName) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ swift.claimTok sn.γcl K (.rest d γi) ∗
      swift.freeSp sn.γcg K.1 ⊢
    |={⊤}=> ∃ rv : swift.RowV, ▷ swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv (swift.recOf (.rest d γi)) := by
  iintro ⟨#HN, Hcl, #Hsp⟩
  iinv HN with Hn Hclose
  iunfold swift.nodeInvD at Hn
  imod Hn
  icases Hn with ⟨%st, %O, Hstn, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  iunfold swift.claimTok at Hcl
  ihave %Hl := ghost_map_lookup $$ Hc Hcl
  have hR : Rt.lookup K = some (swift.recOf (.rest d γi)) := h.2.2.2.2 K _ Hl
  have h' := swift.storeOk_release st.cballot O Rt Out Cl K h (by simp [hR])
  icases (BigSepM.bigSepM_delete (show PartialMap.get? Rt K = some (swift.recOf (.rest d γi))
    from hR)).1 $$ Hm with ⟨⟨%rv, Htok, Hw, Htx⟩, Hm⟩
  imod ghost_map_delete $$ Hc Hcl with Hc
  imod Hclose $$ [Hstn Hw2 He HO HX Ha Hc Hm Hu Htok Htx] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe Hstn Hw2 He HO HX
    isplitl [Ha Hc Hm Hu Htok Htx]
    · iunfold swift.storeD
      iexists Rt.insert K .released, Out, Cl.delete K, U
      iframe Ha Hc Hu
      isplitl [Hm Htok Htx]
      · iapply (BigSepM.bigSepM_insert_delete (Φ := fun (K : Nat × sp.CmdId) (rk : swift.RecK) =>
          iprop(∃ rv : swift.RowV, swift.rowTok γo K.1 K.2 rv ∗
            swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗ swift.tixOr sn.γxu sn.γxm K))).2
        iframe Hm
        iexists rv; iframe Htok Htx
        iapply swift.retWhy_released; iexact Hsp
      ipureintro; exact ⟨h', hU⟩
    ipureintro; exact ⟨Hacc, Hok⟩
  imodintro
  iexists rv
  inext
  iexact Hw

/-- **A stopped descriptor's home, forgotten for the pool** (round 35; table rev 5 C5, T23): a
home whose token is stored takes back the record's halves by its claim (`store_release`). Round
B1 (D82 (4)): with the stopped ballot's spent free permit; round 59: the home's ballot `b` (the
epoch link) is that ballot. -/
theorem swift.descRestS_forget (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat)
    (γsh : GName) (b : Nat) (d : Loc) :
    swift.freeSp sn.γcg b ∗ swift.descRestS γ γv γe γo sn k γsh b d ⊢
      |={⊤}=> swift.descRestA γsh d := by
  iintro ⟨#Hsp, H⟩
  iunfold swift.descRestS at H
  icases H with (H | ⟨#HN, %K, %γi, Hcl, Hh⟩)
  · imodintro; iapply swift.descRestT_A; iexact H
  iunfold swift.descRestH at Hh
  icases Hh with ⟨%q, %ph, %sn', %c, %vs, %dep, %hs, %pd, %sb, %p, %ap, %wa, %sl, %df, Hsh, #Hmx,
    Hph2, Hcmd, #Hvs, %Hop, Hdep2, Hhs, Hsn, Hp2, Hp3, Hpd, Hap, Hocf, Hslw, Hdf, Hwa, Hsb,
    %y, %c0, -, %HK, -⟩
  -- round 59 (D83 (3)): the epoch link's stored disjunct records `K = (b, y)`, so the claim is at
  -- the stopped ballot `b`, whose free permit is spent
  have hK : K.1 = b := by rw [HK.1]
  ihave #HspK : swift.freeSp sn.γcg K.1 $$ []
  · rw [hK]; iexact Hsp
  imod swift.store_release γ γv γe γo sn k K d γi $$ [HN Hcl HspK] with ⟨%rv, Hw⟩
  · iframe HN Hcl HspK
  imod Hw
  simp only [swift.recOf, swift.retWhy]
  icases Hw with ⟨%x, %dv, %Hx, -, Hph, Hdep, Hp, -⟩
  ihave ⟨-, Hph⟩ := typedPointsto_half_combine _ dv.phase ph (1 : Qp) $$ [Hph Hph2]
  · iframe
  ihave ⟨-, Hdep⟩ := typedPointsto_half_combine _ dv.dep dep (1 : Qp) $$ [Hdep Hdep2]
  · iframe
  ihave ⟨-, Hp⟩ := typedPointsto_half_combine _ dv.propose p (1 : Qp).half $$ [Hp Hp3]
  · iframe
  ihave ⟨-, Hp⟩ := typedPointsto_half_combine _ p p (1 : Qp) $$ [Hp Hp2]
  · iframe
  imodintro
  iunfold swift.descRestA
  iexists q, ph, sn', c, vs, dep, hs, pd, sb, p, ap, wa, sl, df
  iframe
  iframe Hmx Hvs
  ipureintro; exact Hop

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
