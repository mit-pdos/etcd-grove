/-
The `defs` package's `NewBeTheLeaderReply()` and `UpdateBeTheLeaderReply(l)` as the master's
`run()` calls them (`NewBeTheLeaderReply.specM`, `UpdateBeTheLeaderReply.specM`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions]

set_option goose.wp.extras true in
theorem replica.defs.NewBeTheLeaderReply.wp_proof : NewBeTheLeaderReply.specM (GF := GF) := by
  wp_start
  wp_auto
  iapply HΦ; iframe

set_option goose.wp.extras true in
theorem replica.defs.UpdateBeTheLeaderReply.wp_proof :
    UpdateBeTheLeaderReply.specM (GF := GF) := by
  intro l
  wp_start as Hl
  wp_auto
  iapply HΦ; iexact Hl

end proof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
