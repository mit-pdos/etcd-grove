/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/NewEncoder.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`gob.NewEncoder(w)`: a new encoder over the writer `w`.
-/
module

public import Dsverify.Spec.encoding.gob.Defs

-- PORT: lab imports dropped: Harness.Proof.bufio.ReadFull, Harness.Proof.bufio.Writer

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [net.rpc.RpcKit] [net.rpc.RpcCodec GF]

/-- `NewEncoder(w)` returns a fresh `*Encoder` holding `w`. -/
abbrev NewEncoder.spec : Prop :=
  ∀ (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob }}
    (App (Val (@! encoding.gob.NewEncoder)) (Val #w))
  {{ (enc : Loc), RET #enc; enc ↦ (⟨w⟩ : encoding.gob.Encoder) }}

end spec

end Perennial.encoding.gob

