/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/gob/NewDecoder.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `Spec/gob/NewDecoder.lean`.
-/
module

public import Dsverify.Proof.encoding.gob.Base
public import Dsverify.Spec.encoding.gob.NewDecoder

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [pkgState : github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [net.rpc.RpcKit] [net.rpc.RpcCodec GF]

theorem NewDecoder.wp_proof : NewDecoder.spec (GF := GF) := by
  intro r
  wp_start
  wp_auto
  iapply HΦ
  iframe

end proof

end Perennial.encoding.gob
