/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/Encoder__EncodeW.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`enc.Encode(v)` over an abstract **sink** (change log C18; additive: `Encoder.Encode.spec`, over
a `*bufio.Writer`, is unchanged). The writer `w` is any `io.Writer` whose `Write` appends the
bytes to an abstract stream `S` (the client group's marshaling sinks, `wire.sinkOk`, unfolded
here: the caller's obligation `□ Q` of the stream extended by the bytes, the stream extended
whatever the result). `swift.MSync.Marshal` (`gob.NewEncoder(w).Encode(m)`) is called by the
replica's `SendToAll` with such a sink (`sp.marshalOk`).
-/
module

public import Dsverify.Spec.encoding.gob.Defs

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

/-- `w.Write` appends to the stream `S` (see the file header). -/
def writeSink (e : GoInterfaceOk) (S Q : List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (dq : DFrac) (W bs : List w8) (Φ : val → IProp GF),
      S W -∗ □ Q (W ++ bs) -∗ p ↦*{dq} bs -∗
      ▷ (∀ (nn : w64) (err : GoInterface), S (W ++ bs) -∗ p ↦*{dq} bs -∗
          Φ (PairV #nn #err)) -∗
      WP (App (Val #(methods e.ty go!"Write" e.v)) (Val #p)) {{ Φ }})

instance writeSink_persistent (e : GoInterfaceOk) (S Q : List w8 → IProp GF) :
    Persistent (writeSink e S Q) := by
  unfold writeSink; infer_instance

/-- `enc.Encode(v)` over the sink `e` (change log C18): the codec encodes `v` (`RpcCodec.enc`:
the bytes `bs` with `Θ bs`, the caller's obligation `□ Q` of the stream extended by the frame),
and the frame `sp.gobFrame bs` is appended to the stream with one `Write`; the error is the
`Write`'s. -/
abbrev Encoder.EncodeW.spec : Prop :=
  ∀ (enc : Loc) (dq : DFrac) (e : GoInterfaceOk) (S Q : List w8 → IProp GF) (W : List w8)
    (v : GoInterface) (Θ : List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ∗ codecSet (GF := GF) ∗
      net.rpc.kitCodecOk (GF := GF) ∗ writeSink e S Q ∗
      enc ↦{dq} (⟨interface.ok e⟩ : encoding.gob.Encoder) ∗ S W ∗
      net.rpc.RpcCodec.enc v (fun bs =>
        iprop(□ Q (W ++ github_com.imdea_software.swiftpaxos.sp.gobFrame bs) ∗ Θ bs)) }}
    (App (Val (enc @!! go.GoType.PointerType encoding.gob.Encoder.ty @!! go!"Encode")) (Val #v))
  {{ (err : GoInterface), RET #err; ∃ bs : List w8, Θ bs ∗
      enc ↦{dq} (⟨interface.ok e⟩ : encoding.gob.Encoder) ∗
      S (W ++ github_com.imdea_software.swiftpaxos.sp.gobFrame bs) }}

end spec

end Perennial.encoding.gob
