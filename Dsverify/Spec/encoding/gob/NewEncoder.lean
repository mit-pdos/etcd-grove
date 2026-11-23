/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/NewEncoder.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`gob.NewEncoder(w)`: a fresh encoder over the writer `w` (Go: `enc.w = []io.Writer{w}`, the
type maps empty).
-/
module

public import Dsverify.Spec.encoding.gob.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetRpc

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

/-- `NewEncoder(w)` returns a fresh `*Encoder` writing to `w`. -/
abbrev NewEncoder.spec : Prop :=
  ∀ (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob }}
    (App (Val (@! encoding.gob.NewEncoder)) (Val #w))
  {{ (enc : Loc), RET #enc; encoding.gob.ownEncoder enc w }}

end spec

end Perennial.encoding.gob
