/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/KitLike.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec instance the linked results use (decision D6, HUB-REQUEST 2), and the laws the proofs
need of any codec they are stated over.

The frozen `kitCodecOk_holds` (Spec/swiftnet/Codec.lean) is false at one point: the harness's
`decOk` asks `rpcDecode` to accept any target, and it panics on a non-zero `MSync`. The harness's
rpc proofs are generic in the `RpcCodec` instance, so the linked results use them at
`examples.swiftnet.kitCodecC` (Proof/swiftnet/codec/Ok.lean): `kitCodec` with `dec` restricted to
the targets the code accepts (`decTarget`). Its `kitCodecOk` is proved with no gap
(`kitCodecOkC_holds`).

* `KitLike C`: what the master's and client's proofs use of their codec `C` (a section
  variable there, so that the frozen statements stay proved at `kitCodec` and the linked ones are
  proved at `kitCodecC`): `C`'s `enc`, `call`, `methods` are `kitCodec`'s, and `C.dec` follows from
  `kitCodec`'s decoding premise on an accepted target (`decT`). Instances for both codecs.
* `kitCodecOkC`, `kitCodecOkC_holds`.
* `rcvrOk_of`, `methods_of`: `kitCodec`'s `rcvrOk`/`methods` facts (the frozen specs' form) give
  `C`'s.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section kitlike
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `kitCodec`'s decoding premise, on a target the code accepts (`decTarget`: not a non-zero
`MSync`). -/
def decT (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF) : IProp GF :=
  iprop(∃ x0 : sp.KitVal, ⌜examples.swiftnet.decTarget x0⌝ ∗ kitValOwn ptr (DFrac.own 1) x0 ∗
    ((∀ y : sp.KitVal, ⌜bs = y.encode ∧ y.tag = x0.tag ∧ sp.KitVal.wf y⌝ -∗
        kitValOwn ptr (DFrac.own 1) (sp.KitVal.merge x0 y) -∗ Ψ true) ∧
      (⌜∀ y : sp.KitVal, y.tag = x0.tag → sp.KitVal.wf y → bs ≠ y.encode⌝ -∗
        ∀ ok : Bool, (∃ x1 : sp.KitVal, ⌜x1.tag = x0.tag⌝ ∗ kitValOwn ptr (DFrac.own 1) x1) -∗
          Ψ ok)))

/-- The laws of `kitCodec` the master's and client's proofs use of their codec. -/
class KitLike (C : net.rpc.RpcCodec GF) : Prop where
  enc_eq : @net.rpc.RpcCodec.enc _ GF C = @net.rpc.RpcCodec.enc _ GF kitCodec
  call_eq : @net.rpc.RpcCodec.call _ GF C = @net.rpc.RpcCodec.call _ GF kitCodec
  methods_eq : @net.rpc.RpcCodec.methods _ GF C = @net.rpc.RpcCodec.methods _ GF kitCodec
  dec_intro : ∀ (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF),
    decT bs ptr Ψ ⊢ @net.rpc.RpcCodec.dec _ GF C bs ptr Ψ

instance kitLike_kitCodec : KitLike (kitCodec (GF := GF)) where
  enc_eq := rfl
  call_eq := rfl
  methods_eq := rfl
  dec_intro bs ptr Ψ := by
    unfold decT
    iintro ⟨%x0, -, Hown, Hk⟩
    unfold kitCodec; dsimp only
    iexists x0
    iframe

theorem kitValOwnC_eq : @kitValOwnC _ _ _ _ GF _ _ = @kitValOwn _ _ _ _ GF _ _ := rfl
theorem mergeC_eq : @sp.KitVal.mergeC = @sp.KitVal.merge := rfl
theorem wfC_eq : @sp.KitVal.wfC = @sp.KitVal.wf := rfl

instance kitLike_kitCodecC : KitLike (examples.swiftnet.kitCodecC (GF := GF)) where
  enc_eq := rfl
  call_eq := rfl
  methods_eq := rfl
  dec_intro bs ptr Ψ := by
    unfold decT
    iintro ⟨%x0, %Ht, Hown, Hk⟩
    unfold examples.swiftnet.kitCodecC; dsimp only
    simp only [kitValOwnC_eq, mergeC_eq, wfC_eq]
    iexists x0
    iframe
    ipureintro; exact Ht

theorem rcvrOk_of (C : net.rpc.RpcCodec GF) [KitLike C] (r : GoInterface)
    (S : net.rpc.MethodSpec GF) :
    @net.rpc.rcvrOk _ GF kitCodec r S ⊢ @net.rpc.rcvrOk _ GF C r S := by
  unfold net.rpc.rcvrOk
  rw [KitLike.call_eq (C := C)]

theorem methods_of (C : net.rpc.RpcCodec GF) [KitLike C] (r : GoInterface) :
    @net.rpc.RpcCodec.methods _ GF kitCodec r ⊢ @net.rpc.RpcCodec.methods _ GF C r := by
  rw [KitLike.methods_eq (C := C)]

theorem enc_of (C : net.rpc.RpcCodec GF) [KitLike C] (v : GoInterface) (Ψ : List w8 → IProp GF) :
    @net.rpc.RpcCodec.enc _ GF kitCodec v Ψ ⊢ @net.rpc.RpcCodec.enc _ GF C v Ψ := by
  rw [KitLike.enc_eq (C := C)]

variable [HasExt netExt] [net.Assumptions] [net.FieldAssumptions]
  [net.rpc.Assumptions] [examples.swiftnet.Assumptions]

/-- The harness's codec obligations at `kitCodecC`. -/
abbrev kitCodecOkC : IProp GF := @net.rpc.kitCodecOk _ _ _ _ GF _ _ _ examples.swiftnet.kitCodecC

/-- `kitCodecOkC` holds: no gap (the codec group's `encOkC`, `decOkC`, `methodsOkC`,
`callOkC`). -/
theorem kitCodecOkC_holds : ⊢ kitCodecOkC (GF := GF) := by
  unfold kitCodecOkC net.rpc.kitCodecOk
  isplitr
  · iapply examples.swiftnet.encOkC
  isplitr
  · iapply examples.swiftnet.decOkC
  isplitr
  · iapply examples.swiftnet.methodsOkC
  · iapply examples.swiftnet.callOkC

end kitlike

end Perennial.github_com.imdea_software.swiftpaxos
