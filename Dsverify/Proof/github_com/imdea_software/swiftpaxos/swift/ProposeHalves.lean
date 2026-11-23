/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ProposeHalves.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
A proposal's read-only record (`swift.propIs`, D16) is what `ProposeChan` carries
(`sp.proposeP`), to send it again (`handleSync`'s re-proposals).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Local

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- **A proposal sent again** (`handleSync`'s re-proposals): its read-only record is what
`ProposeChan` carries (D16). -/
theorem swift.propIs_proposeP (γ : sp.Names) (gp : Loc) (x : sp.CmdId) (c : sp.Cmd) :
    swift.propIs γ gp x c ⊢ sp.proposeP γ gp := by
  unfold swift.propIs
  iintro ⟨%p, %w, %mu, %addr, %ts, %vs, #Hg, #Hp, #Hv, #Hc, %Hwf⟩
  unfold sp.proposeP
  iexists p, w, mu, addr, x.seq, x.cl, c, ts, vs
  iframe Hg Hp Hv Hc
  ipureintro; exact Hwf.1

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
