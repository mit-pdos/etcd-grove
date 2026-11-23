/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swiftnet/registerRPC.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`registerRPC()` (`examples/swiftnet/rpc_model_gen.go`, generated): registers the kit's codec with
the net/rpc model (`rpc.SetCodec`) and with the encoding/gob model (`gob.SetCodec`).
-/
module

public import Dsverify.Spec.encoding.gob.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [SwiftNetPkgState GF]
variable [examples.swiftnet.Assumptions]

/-- `registerRPC()`, after the test package's initialization: both models' codecs hold the kit's
functions, for good (each call registers them; the first registration stays). Called by `New`
(client node) and `serve` (server nodes), possibly more than once per node. -/
abbrev registerRPC.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet }}
    (App (Val (@! examples.swiftnet.registerRPC)) (Val #()))
  {{ RET #(); net.rpc.codecSet (GF := GF) net.rpc.RpcCodec.spec ∗ encoding.gob.codecSet (GF := GF) }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
