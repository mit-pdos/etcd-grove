/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncStep.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's ghost step for taking an `MSync` (`handleSync`): through the node invariant
(`swift.run_upd`), one `sp.upd_takeSync`. The acceptances' bound of `nodeInv` gives
`upd_takeSync`'s "nothing accepted in `b'`" (`b' > cballot`), and is kept (the new acceptances
are of `b'`, the new `cballot`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The view after taking ballot `b'`'s `MSync` of order `o`. -/
def swift.LView.tookSync (w : swift.LView) (b' : Nat) (o : List sp.CmdId) : swift.LView :=
  (b', b', true, (b', o) :: w.2.2.2)

theorem swift.LView.tookSync_locAt (w : swift.LView) (b' : Nat) (o : List sp.CmdId) (b : Nat) :
    (w.tookSync b' o).locAt b = if b = b' then o else w.locAt b := by
  unfold swift.LView.tookSync swift.LView.locAt
  by_cases h : b = b'
  · subst h; simp
  · simp [h, Ne.symm h]

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
