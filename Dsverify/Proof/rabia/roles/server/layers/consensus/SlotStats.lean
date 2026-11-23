/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/SlotStats.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server/layers/consensus.(*Consensus).SlotStats`.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Spec
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS]

theorem Consensus.SlotStats.wp_proof : Consensus.SlotStats.spec (GF := GF) := fun c => by
  wp_start as #Hs
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ [Hpkg]
  · iPkgInit
  unfold consStatsRO
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hs] as ⟨Hlocked, Hinv⟩
  unfold statInv
  icases Hinv with ⟨%a, %b, %d, %e, Ha, Hb, Hd, He⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hs $Hlocked Ha Hb Hd He]
  · inext
    iexists a, b, d, e
    iframe
  iapply HΦ
  itrivial

end proof
end Perennial.rabia.roles.server.layers.consensus
