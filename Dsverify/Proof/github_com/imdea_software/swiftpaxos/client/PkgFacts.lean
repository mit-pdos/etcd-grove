/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/PkgFacts.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Change log C6** (with C10's `defs.LatencyConf`): the package-level variables the client node
reads, as facts of the swift and defs package states on the client node (a marked hypothesis of
the client group's proofs until those package states are proved; owner: the swift prover).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- **Change log C6**: the package-level variables the client node reads, as facts of the swift
package's state on the client node: `ReplyHook` is nil (set only under the `swiftexeclog` build
tag), the fast-ack pool is off (only `swift.New`, never called on the client node, sets it), and
`errVarintOverflow` holds an error (its initializer's `errors.New`); and of the defs package's
state: `defs.LatencyConf` is `""` (only a replica's flags set it; `Connect` then leaves the
client's latency table nil). Owner: the package states (`SwiftNetPkgState`); until they are
proved, `NewClient`'s and `Connect`'s proofs take this record as a marked hypothesis. -/
structure ClientPkgFacts : Prop where
  pkgFacts : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢
    globalAddr swift.ReplyHook ↦□ func.nil ∗ globalAddr swift.useFastAckPool ↦□ false ∗
    ∃ ov : GoInterface, globalAddr swift.errVarintOverflow ↦□ ov ∗ ⌜ov ≠ interface.nil⌝)
  latencyConf : (isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs ⊢
    typedPointsto (globalAddr replica.defs.LatencyConf) (go!"" : GoString) DFrac.discard)

end defs

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
