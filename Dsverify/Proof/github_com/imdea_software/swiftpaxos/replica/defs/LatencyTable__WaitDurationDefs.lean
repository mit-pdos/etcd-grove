/-
The definitions, specs and lemmas of `LatencyTable__WaitDuration.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.replica.defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [replica.defs.Assumptions]

/-- `WaitDuration` on a nil table: no wait. -/
abbrev replica.defs.LatencyTable.WaitDuration.specNil : Prop :=
  ∀ (addr : GoString),
  {{ (True : IProp GF) }}
    (App (Val (null @!! go.GoType.PointerType replica.defs.LatencyTable.ty @!! go!"WaitDuration"))
      (Val #addr))
  {{ RET #(W64 0); True }}

set_option goose.wp.extras true

end proof

end Perennial.github_com.imdea_software.swiftpaxos
