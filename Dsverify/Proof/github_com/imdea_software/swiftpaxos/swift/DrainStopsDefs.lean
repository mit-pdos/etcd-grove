/-
The definitions, specs and lemmas of `DrainStops.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SlotSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- Two signal tokens of one incarnation exclude each other. -/
theorem swift.sgTok_excl (γsg : GName) : swift.sgTok γsg ∗ swift.sgTok γsg ⊢ (False : IProp netDistGF) := by
  iintro ⟨H1, H2⟩
  iunfold swift.sgTok at H1 H2
  ihave %Hv := ghostVar_valid_2 γsg true (1 : Qp) true (1 : Qp) $$ H1 H2
  exfalso
  obtain ⟨hq, -⟩ := Hv
  revert hq
  simp only [Qp.le_iff, Qp.val_add, Qp.val_one]
  intro h
  grind

/-- What a queued request leaves with the caller (the loop's invariant): the token, or the
element's half. -/
theorem swift.drainStops_step (γs γsg : GName) (k : GoString) (d sc wg : Loc) :
    swift.stopMP γs γsg k d sc wg ∗
      (swift.sgTok γsg ∨ ghostMapElem γs k (DFrac.own (1 : Qp).half) true) ⊢
    sync.join.ownDone wg (ghostMapElem γs k (DFrac.own 1) true) ∗
      ghostMapElem γs k (DFrac.own 1) true ∗ swift.sgTok γsg := by
  iintro ⟨Hm, Ht⟩
  iunfold swift.stopMP at Hm
  icases Hm with ⟨Hd, Htok, Hh⟩
  icases Ht with (Ht | Hh2)
  · iexfalso; iapply swift.sgTok_excl γsg $$ [Htok Ht]; iframe
  · iframe Hd Htok
    iapply (ghostMapElem_halves γs k true).2 $$ [Hh Hh2]
    iframe

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
