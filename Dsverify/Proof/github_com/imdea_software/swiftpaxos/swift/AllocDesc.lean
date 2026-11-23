/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AllocDesc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.allocDesc()` (swift.go:948; round 21, sv-swb): a descriptor at rest, from the pool (`Get`:
one `Put` by `freeDesc`, or a fresh one of the pool's `New`) or a fresh `&commandDesc{}`. A
fresh descriptor enters the share map `γsh` (`swift.descPooled_fresh`, by `swift.shInv_fresh`:
it owns `successorsL` whole, so it is not a key yet).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FreeDesc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
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

theorem swift.Replica.allocDesc.wp_proof : swift.Replica.allocDesc.specA (hG := hG) := by
  intro rp γsh
  wp_start as ⟨#Hctx, #Hinv⟩
  iapply wp_fupd
  iunfold swift.descPoolCtx at Hctx
  icases Hctx with ⟨%pl, #Hpl, #Hp⟩
  wp_auto_lc 1
  wp_if_destruct
  · icases Hp with (%Hle | ⟨%pf, %Hpf, #Hp⟩)
    · exfalso; word
    wp_apply sync.Pool.wp_Get $$ [$Hp] as %x ⟨Hx, -⟩
    icases Hx with (Hx | ⟨%Hf, -⟩)
    · iunfold swift.descPoolP at Hx
      icases Hx with ⟨%d, %Hxe, Hd⟩
      subst Hxe
      wp_auto
      icases Hd with (Hd | Hd)
      · imodintro; iapply HΦ; iexact Hd
      · imod swift.descPooled_fresh γsh d $$ [Hinv Hlc1 Hd] with Hd
        · iframe Hinv Hlc1 Hd
        imodintro; iapply HΦ; iexact Hd
    · exact absurd Hf Hpf
  · imod swift.descPooled_fresh γsh «$r0_ptr» $$ [Hinv Hlc1 «$r0»] with Hd
    · iframe Hinv Hlc1; iexact «$r0»
    imodintro; iapply HΦ; iexact Hd

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
