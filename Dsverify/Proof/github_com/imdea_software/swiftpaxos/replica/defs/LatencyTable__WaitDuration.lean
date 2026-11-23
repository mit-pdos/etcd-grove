/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/defs/LatencyTable__WaitDuration.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*defs.LatencyTable).WaitDuration(addr)` on a nil table (the client node's: `Connect` sets
`c.dt = nil` when `defs.LatencyConf` is `""`): returns 0 (replica/defs/latency.go:212). An
internal spec of the `defs` package, proved from its code; the client's readers use it.
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

theorem replica.defs.LatencyTable.WaitDuration.wp_proofNil :
    replica.defs.LatencyTable.WaitDuration.specNil (GF := GF) := by
  intro addr
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos
