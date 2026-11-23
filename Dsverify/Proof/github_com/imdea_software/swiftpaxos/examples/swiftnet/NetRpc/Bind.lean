/-
What the receivers' proofs (`master/Rcvr.lean`, `swift/Rcvr.lean`: the generated `rpcReceiver`
of `examples/swiftnet/rpc_model_gen.go` meets Net's `rcvrIs`) share: the generated `Method` of a
method's three functions (`mOf`), a method's `NewArg` obligation (`newArgOk`, `methodOk`'s body,
and `methodOk_of`), the kit's `RpcCodec.spec` as `swiftCodec` (`rpcCodec_spec_eq`), and a pure
fact read off a `withErr` deposit without consuming it (`withErr_pure`). As dsv-epaxos's
`NetRpc/Bindings.lean`'s first part.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.CodecSrv
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.imdea_software.swiftpaxos

/-- The generated `Method` of the functions named `na`, `nr`, `cl`. -/
abbrev mOf [GooseExts] [GoSemanticsFunctions] [GoGlobalContext] (na nr cl : GoString) :
    net.rpc.Method :=
  net.rpc.Method.mk (functions na []) (functions nr []) (functions cl [])

section bind
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [examples.swiftnet.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What a method's `NewArg` must meet (`methodOk`'s body). -/
def newArgOk (C : net.rpc.CodecSpec GF) (rcvr : GoInterface) (Sm : net.rpc.MSpec GF)
    (v : net.rpc.Method) : IProp GF :=
  iprop(□ ∀ Ψ : val → IProp GF,
      ▷ (∀ (argv : GoInterface) (D : IProp GF) (Θ : List w8 → Bool → IProp GF),
          ⌜argv ≠ interface.nil⌝ -∗ net.rpc.argDec C argv D Sm Θ -∗ D -∗
          (∀ (args : List w8) (Φ : List w8 → GoString → IProp GF), Sm args Φ -∗ Θ args true -∗
            net.rpc.callObl C rcvr v argv Φ) -∗ Ψ #argv) -∗
      WP (App (Val #v.NewArg') (Val #())) {{ Ψ }})

instance newArgOk_persistent (C : net.rpc.CodecSpec GF) (rcvr : GoInterface)
    (Sm : net.rpc.MSpec GF) (v : net.rpc.Method) :
    Persistent (newArgOk (hG := hG) C rcvr Sm v) := by
  unfold newArgOk; infer_instance

theorem methodOk_of (C : net.rpc.CodecSpec GF) (rcvr : GoInterface) (Sm : net.rpc.MSpec GF)
    (mm : Loc) (v : net.rpc.Method) :
    mm ↦□ v ∗ newArgOk C rcvr Sm v ⊢ net.rpc.methodOk C rcvr Sm mm := by
  unfold net.rpc.methodOk newArgOk
  iintro ⟨#Hm, #Hn⟩
  iexists v
  iframe Hm
  iexact Hn

/-- The kit's codec (`kitCodec`'s fields) is the generated one. -/
theorem rpcCodec_spec_eq : net.rpc.RpcCodec.spec (GF := GF) = swiftCodec := rfl

theorem swiftCodec_rcv_eq (rcvr : GoInterface) (Ψ : Loc → IProp GF) :
    swiftCodec.rcv rcvr Ψ = iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
      WP (App (Val #(functions examples.swiftnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }}) := rfl

end bind

section werr
open Dsv in
attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [SwiftNetPkgState GF] [net.rpc.Assumptions] [net.FieldAssumptions]

/-- A pure fact of a deposit's spec, read off a `withErr` deposit (which stays). -/
theorem withErr_pure (S : net.rpc.MethodSpec GF) (m : GoString) (args : List w8)
    (Φ : List w8 → GoString → IProp GF) (φ : Prop) (h : S m args Φ ⊢ ⌜φ⌝) :
    withErr S m args Φ ⊢ ⌜φ⌝ ∗ withErr S m args Φ := by
  refine (and_intro ?_ .rfl).trans persistent_and_sep_mp
  unfold withErr
  exact and_elim_l.trans h

end werr

end github_com.imdea_software.swiftpaxos

end Perennial
