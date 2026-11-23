/-
The definitions, specs and lemmas of `SlotProofS.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SlotSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- A history slot's message of the epoch's predicate is in the history's bounds, and `y` was
executed in the epoch (table §3R11a 11a.4, C2: `slotMP` through `mpOk`). -/
theorem swift.mp_slot (x : swift.RunX) (γ : sp.Names) (γc γm : GName) (rp : Loc) (g : swift.DescG)
    (y : swift.CommandId) (s : w64) (h : swift.mpOk x γ γc γm rp g) :
    g.mp y (interface.mkOk go.int #s) ⊢ ⌜swift.slotIn s⌝ ∗ swift.exIn x.γxm g.ev.b y := by
  rw [h]
  iintro H
  iunfold swift.descMP at H
  icases H with (Ha | ⟨%pm, %gp, %cc, %dep, %hs, %sq, %ld, %s', %B, %D, %P, %H', %Hm, -⟩ | Hs | Hse)
  · iunfold swift.ackMsgP at Ha
    icases Ha with (⟨%l, %fa, ⟨%Hm, -⟩, -⟩ | ⟨%l, %sa, %Hm, -⟩ | %Hm)
    · exfalso; simp only [interface.mkOk] at Hm; injection Hm with h1; injection h1 with h2; cases h2
    · exfalso; simp only [interface.mkOk] at Hm; injection Hm with h1; injection h1 with h2; cases h2
    · exfalso; obtain ⟨str, Hm⟩ := Hm; simp only [interface.mkOk] at Hm; injection Hm with h1
      injection h1 with h2; cases h2
  · exfalso; simp only [interface.mkOk] at Hm; injection Hm with h1; injection h1 with h2; cases h2
  · iunfold swift.slotMP at Hs
    icases Hs with ⟨%s', ⟨%Hm, %Hin⟩, #Hex⟩
    simp only [interface.mkOk] at Hm; injection Hm with h1; injection h1 with _ h2
    have := go.intoVal_inj h2
    subst this
    iframe Hex
    ipureintro; exact Hin
  · iunfold swift.syncMP at Hse
    icases Hse with ⟨%se, %gp, %c, %vs, %dsl, %D, %M, %i, %Hm, -⟩
    exfalso; simp only [interface.mkOk] at Hm; injection Hm with h1; injection h1 with h2; cases h2

end lemmas

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

set_option goose.wp.extras true

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
