/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/FreeDesc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.freeDesc(desc)` (swift.go:957; round 16, sv-swb): with the pool on (`poolLevel > 0`) the
descriptor goes to `descPool` (predicate `descPoolP DF`), else it is dropped. Spec:
`swift.Replica.freeDesc.specI` (SyncSpecs.lean, restated in round 16 with `descPoolCtx`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [sync.Assumptions]

/-- **`freeDesc`**: `Put` with `descPoolP DF` when `poolLevel > 0`. No callee hypothesis
(`sync.Pool.wp_Put` is Perennial's). -/
theorem swift.Replica.freeDesc.wp_proof (DF : Loc → IProp netDistGF) :
    swift.Replica.freeDesc.specI (hG := hG) DF := by
  intro rp d
  wp_start as ⟨#HctxF, Hd⟩
  -- round 35 (C5, T23): the rest turned into the pool's
  iunfold swift.descPoolCtxF at HctxF
  icases HctxF with ⟨%DFp, #Hctx, #Hlaw⟩
  iunfold swift.descPooled at Hd
  icases Hd with ⟨%m, %s, %sl, %fa, Hm, Hs, Hsl, Hfa, Hsl', Hfa', HDF⟩
  iapply fupd_wp
  imod Hlaw $$ %d HDF with HDF
  imodintro
  ihave Hd : swift.descPooled DFp d $$ [Hm Hs Hsl Hfa Hsl' Hfa' HDF]
  · iunfold swift.descPooled; iexists m, s, sl, fa; iframe
  iunfold swift.descPoolCtx at Hctx
  icases Hctx with ⟨%pl, #Hpl, #Hp⟩
  wp_auto
  wp_if_destruct
  · icases Hp with (%Hle | ⟨%pf, -, #Hp⟩)
    · exfalso; word
    wp_apply sync.Pool.wp_Put $$ [Hd]
    · iframe Hp
      iunfold swift.descPoolP
      iexists d
      isplitr
      · ipureintro; rfl
      ileft; iexact Hd
    try wp_auto
    iapply HΦ; itrivial
  · iapply HΦ; itrivial

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
