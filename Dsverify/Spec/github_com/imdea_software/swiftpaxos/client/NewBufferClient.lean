/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/NewBufferClient.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`client.NewBufferClient(cl, reqNum, 0, 0, 0, 0)` (the adapter's `connect`, `reqNum = K`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [client.Assumptions]

/-- The buffer client of a fresh client with id `cid` (its reply channel buffered
`reqNum + 1`). -/
abbrev client.NewBufferClient.spec : Prop :=
  ∀ (cl : Loc) (cid : w32) (maddr : GoString) (mport reqNum : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      -- change log C4: `reqNum < 2 ^ 32 - 1` (the channel's capacity `reqNum + 1`)
      client.fresh cl cid maddr mport ∗ ⌜0 ≤ sint.Z reqNum ∧ sint.Z reqNum < 2 ^ 32 - 1⌝ }}
    (App (App (App (App (App (App (Val (@! client.NewBufferClient)) (Val #cl)) (Val #reqNum))
      (Val #(W64 0))) (Val #(W64 0))) (Val #(W64 0))) (Val #(W64 0)))
  {{ (b : Loc), RET #b; client.bufFresh b cid maddr mport }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
