/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/Decoder__Decode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`dec.Decode(ptr)` over an `io.Reader` (a replica's peer `*bufio.Reader` in `MSync.Unmarshal`:
`bufio.bufioReadsOk`): reads exactly one frame (`io.ReadFull` of its 8-byte length, then of its
body) and decodes the body into `*ptr` with the codec.
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

/-- `dec.Decode(ptr)`: the reader delivers `data`; `nil` exactly when `data` is one whole
frame `gobFrame bs` (`bs` shorter than `2 ^ 64`, change log C17) and the codec decoded `bs` into
`ptr` (`Ψ bs true`); otherwise an error
(with some message) after a short read or a frame over `MaxFrame` (the decoding resource `D`
back) or a failed decoding (`Ψ bs false`). The decoding premise is given for whatever body is
read: `□ (D -∗ ∀ bs, RpcCodec.dec bs ptr (Ψ bs))`. -/
abbrev Decoder.Decode.spec : Prop :=
  ∀ (dec : Loc) (dq : DFrac) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (ptr : GoInterface) (D : IProp GF) (Ψ : List w8 → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ∗ codecSet (GF := GF) ∗
      net.rpc.kitCodecOk (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      bufio.readsOk rd I ∗ I R ∗ encoding.gob.ownDecoder dec dq (rd) ∗
      D ∗ □ (D -∗ ∀ bs, net.rpc.RpcCodec.dec bs ptr (Ψ bs)) }}
    (App (Val (dec @!! go.GoType.PointerType encoding.gob.Decoder.ty @!! go!"Decode"))
      (Val #ptr))
  {{ (e : GoInterface), RET #e; encoding.gob.ownDecoder dec dq (rd) ∗
      ∃ data : List w8, I (R ++ data) ∗
      -- change log C17 (SWC-G1): the frame's body is shorter than `2 ^ 64` (its length is an
      -- 8-byte field)
      ((⌜e = interface.nil⌝ ∗ ∃ bs, ⌜data = github_com.imdea_software.swiftpaxos.sp.gobFrame bs ∧
          bs.length < 2 ^ 64⌝ ∗ Ψ bs true) ∨
        (⌜e ≠ interface.nil⌝ ∗ net.rpc.errAny e ∗
          (D ∨ ∃ bs, ⌜data = github_com.imdea_software.swiftpaxos.sp.gobFrame bs⌝ ∗ Ψ bs false))) }}

end spec

end Perennial.encoding.gob

