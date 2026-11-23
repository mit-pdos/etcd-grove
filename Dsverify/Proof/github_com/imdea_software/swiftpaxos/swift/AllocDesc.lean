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

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AllocDescDefs

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

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

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
