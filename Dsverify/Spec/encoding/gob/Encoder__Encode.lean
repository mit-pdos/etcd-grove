/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/Encoder__Encode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`enc.Encode(v)` over a `*bufio.Writer` (as `swift.MSync.Marshal` uses it, on a replica's peer
writer): one frame, `sp.gobFrame` of the codec's encoding of `v`, given to the writer with one
`Write`.
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

/-- `enc.Encode(v)`, `enc` over the `*bufio.Writer` `bw` (`bufio.ownWriter`, over the
underlying `wr`): the codec encodes `v` (`RpcCodec.enc`: the bytes `bs` with `Θ bs`, the
caller's obligation `□ Q` of the writer's stream extended by the frame included), and
`bw.Write(gobFrame bs)` takes the frame or, on an error, a prefix of it (`Writer.Write`'s
contract, `bufio.wp_Write`); the error is the `Write`'s. -/
abbrev Encoder.Encode.spec : Prop :=
  ∀ (enc : Loc) (dq : DFrac) (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (v : GoInterface) (Θ : List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ∗ codecSet (GF := GF) ∗
      net.rpc.kitCodecOk (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
      bufio.writerOk wr J Q ∗
      encoding.gob.ownEncoder enc dq (interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw) ∗
      bufio.ownWriter bw wr J Q sent pend err ∗
      net.rpc.RpcCodec.enc v (fun bs =>
        iprop(□ Q (sent ++ pend ++ github_com.imdea_software.swiftpaxos.sp.gobFrame bs) ∗ Θ bs)) }}
    (App (Val (enc @!! go.GoType.PointerType encoding.gob.Encoder.ty @!! go!"Encode")) (Val #v))
  {{ (e : GoInterface), RET #e; ∃ (bs : List w8) (k : Nat) (sent' pend' : List w8),
      ⌜k ≤ (github_com.imdea_software.swiftpaxos.sp.gobFrame bs).length ∧
        sent' ++ pend' = sent ++ pend ++ (github_com.imdea_software.swiftpaxos.sp.gobFrame bs).take k ∧
        sent <+: sent' ∧
        (e = interface.nil → k = (github_com.imdea_software.swiftpaxos.sp.gobFrame bs).length) ∧
        (err ≠ interface.nil → e = err ∧ k = 0)⌝ ∗
      Θ bs ∗
      encoding.gob.ownEncoder enc dq (interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw) ∗
      bufio.ownWriter bw wr J Q sent' pend' e }}

end spec

end Perennial.encoding.gob

