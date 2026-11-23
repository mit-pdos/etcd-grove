/-
**Step 5, the codec (started).** The kit's generated net/rpc codec (`examples/swiftnet/rpc_gen.go`,
by `models/net/rpc/rpcgen.py` from `rpc.toml`; registered by `rpc_model_gen.go`'s `Register()`,
`rpcmodel.SetCodec(&Codec{rpcEncode, rpcDecode, rpcReceiver})`) as the specs see it, after
dsv-craq's `Craq/Codec.lean`.

**The `CodecSpec`** (`swiftCodec`): each predicate transformer is the weakest precondition of the
generated function it describes (`rpcEncode`, `rpcDecode`, `rpcReceiver`), so the codec meets
`Net/`'s `encOk`/`decOk`/`rcvOk` by definition (`swiftCodec_encOk`, `_decOk`, `_rcvOk`), and
`codecSet swiftCodec` is what `Register()` leaves (`SetCodec.spec`).

It replaces the lab's kitgen codec (`net.rpc.RpcCodec`, `KitLike`, `kitCodec`, `Spec/.../swiftnet/
Codec.lean`, the lab codec proofs `examples/swiftnet/codec/*`, `swift/CodecFns`, `master/Rcvr`,
`swift/Rcvr`). **Still to do** (notes/dsv-swiftpaxos.md, "Step 5"): `sp.KitVal.encode` (`Spec/swift/
Wire.lean`) restated as rpcgen's bytes (`rpcPutTag` of the type's name, a presence byte per
struct, a presence byte and the value per field that is sent, gob's zero fields omitted; so
decoding into a non-zero target merges, which `KitVal.merge` already models); the per-type
lemmas (`enc_*`, `dec_*`, as craq's `CodecProof.lean`) over the generated `rpcEnc_t*`/`rpcDec_t*`;
`master.rcvr.spec` and the replica's of `rpcReceiver`; then every `RpcCodec.spec`/`kitCodec` use
switched to `swiftCodec`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Net.Proof.net.rpc.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [examples.swiftnet.Assumptions]

/-- The codec's predicate transformers: the generated functions' weakest preconditions. -/
def swiftCodec : net.rpc.CodecSpec GF where
  enc v Ψ := iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sl : GoSlice) (bs : List w8), sl ↦* bs -∗ ownSliceCap w8 sl (DFrac.own 1) -∗ Ψ bs -∗
        Φ #sl) -∗
    WP (App (Val #(functions examples.swiftnet.rpcEncode [])) (Val #v)) {{ Φ }})
  dec bs ptr Ψ := iprop(∀ (data : GoSlice) (dq : DFrac) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else net.rpc.decErr err) -∗ Φ #err) -∗
    WP (App (App (Val #(functions examples.swiftnet.rpcDecode [])) (Val #data)) (Val #ptr)) {{ Φ }})
  rcv rcvr Ψ := iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
    WP (App (Val #(functions examples.swiftnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }})

theorem swiftCodec_encOk :
    ⊢ net.rpc.encOk (hG := hG) swiftCodec (functions examples.swiftnet.rpcEncode []) := by
  unfold net.rpc.encOk
  iintro !> %v %Ψ %Φ Henc HΦ
  unfold swiftCodec
  iapply Henc
  iexact HΦ

theorem swiftCodec_rcvOk :
    ⊢ net.rpc.rcvOk (hG := hG) swiftCodec (functions examples.swiftnet.rpcReceiver []) := by
  unfold net.rpc.rcvOk
  iintro !> %rcvr %Ψ %Φ Hr HΦ
  unfold swiftCodec
  iapply Hr
  iexact HΦ

theorem swiftCodec_decOk :
    ⊢ net.rpc.decOk (hG := hG) swiftCodec (functions examples.swiftnet.rpcDecode []) := by
  unfold net.rpc.decOk
  iintro !> %data %dq %bs %ptr %Ψ %Φ Hd Hdec HΦ
  unfold swiftCodec
  iapply Hdec $$ Hd
  iexact HΦ

end codec

end Perennial.github_com.imdea_software.swiftpaxos
