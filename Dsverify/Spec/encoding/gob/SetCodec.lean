/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/SetCodec.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`gob.SetCodec(c)`: registers the kit's codec (the first registration stays).
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
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [net.rpc.RpcKit] [net.rpc.RpcCodec GF]

/-- `SetCodec(c)` for a codec holding the kit's functions: afterwards the model's codec is
one with the kit's functions, for good (`codecSet`; the first registration wins, and every
registration holds the same functions). -/
abbrev SetCodec.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ∗ ⌜c ≠ null⌝ ∗ codecFns (GF := GF) c }}
    (App (Val (@! encoding.gob.SetCodec)) (Val #c))
  {{ RET #(); codecSet (GF := GF) }}

end spec

end Perennial.encoding.gob

