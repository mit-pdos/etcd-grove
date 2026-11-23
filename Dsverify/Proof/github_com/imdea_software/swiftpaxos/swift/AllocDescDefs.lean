/-
The definitions, specs and lemmas of `AllocDesc.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- **`r.allocDesc()`**: a descriptor at rest at the share map `γsh` (its element whole). -/
abbrev swift.Replica.allocDesc.specA : Prop :=
  ∀ (rp : Loc) (γsh : GName),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.descPoolCtx (swift.descDFA γsh) rp ∗ inv swift.shN (swift.shInv γsh) }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"allocDesc")) (Val #()))
  {{ (d : Loc), RET #d; swift.descPooled (swift.descDFA γsh) d }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

/-- **A fresh descriptor is at rest** (it enters the share map with share `1`). -/
theorem swift.descPooled_fresh (γsh : GName) (d : Loc) :
    inv swift.shN (swift.shInv γsh) ∗ £ 1 ∗ d ↦ (Perennial.zero_val swift.commandDesc) ⊢
    |={⊤}=> swift.descPooled (swift.descDFA γsh) d := by
  iintro ⟨#Hinv, Hlc, Hd⟩
  ihave Hn := ownSlice_nil (V := w8) (GF := netDistGF) (DFrac.own 1)
  imod ownSlice_persist _ _ _ $$ Hn with #Hn
  iStructNamed Hd
  imod swift.shInv_fresh γsh d 1 $$ [Hinv Hlc successorsL successors] with ⟨#Hmx, He⟩
  · iframe Hinv Hlc
    isplitl [successorsL]
    · iexact successorsL
    inext
    iunfold swift.succInv
    iexists slice.nil, []
    iframe successors
    isplitr
    · iapply (ownSlice_nil (V := swift.CommandId) (DFrac.own 1))
    · iapply ownSliceCap_nil
  imodintro
  iunfold swift.descPooled
  iexists _, _, _, _
  iframe msgs stopChan slowPathH fastPathH
  isplitr
  · iunfold swift.msetAny; ileft; ipureintro; rfl
  isplitr
  · iunfold swift.msetAny; ileft; ipureintro; rfl
  simp only [swift.descDFA]
  iunfold swift.descDF
  iexists _, _
  iframe active seq
  isplitr
  · ipureintro; intro h; cases h
  iunfold swift.descRestA
  iexists 1, _, _, ⟨W8 0, W64 0, []⟩, slice.nil, _, _, _, _, _, _, _, _
  iframe He Hmx phase dep hs seqnum propose proposeDep afterPropagate slowPath defered waitingAck storedBallots
  isplitl [cmd]
  · iExactEq cmd; rfl
  isplitr
  · iexact Hn
  isplitr
  · ipureintro; decide
  iunfold swift.ocfAny; ileft; ipureintro; rfl

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
