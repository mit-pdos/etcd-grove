/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: its net/rpc codec

The driver's codec as Net's `CodecSpec` (`Net/Proof/net/rpc/Codec.lean`): the generated functions'
(`examples/net/rpcdriver/rpc_gen.go`, `rpc_model_gen.go`, by `models/net/rpc/rpcgen.py`) weakest
preconditions (`drvCodec`, as swiftnet's `swiftCodec`), and the laws the driver's proofs use,
stated here: proved in `CodecProof.lean` (`drvCodecLaws`) and `Rcvr.lean` (the receivers).

* the client: encoding its request `*service.Args` gives `Wire.lean`'s `encArgs` (`enc_Args`), and
  decoding a reply's bytes `encReply id data runs` into its `&service.Reply{}` succeeds and gives
  back `id`, `data` (in a fresh slice) and `runs` (`dec_Reply`; gob's rule, a field the bytes do not
  send keeps its value, gives the same here, as the target is the zero value);
* the server's bindings (`rpcNewArg_r0_Echo`, ...): decoding a deposit's `encArgs id data fail`
  into `NewArg()`'s fresh `*service.Args` succeeds and gives the values back (`decA_Args`), and
  encoding the method's `*service.Reply` gives `encReply` (`enc_Reply`);
* the receivers (`rpcReceiver`): a `*service.Svc` meets Net's `rcvrIs` with the service's spec
  `echoSvc γid` (`svcRcv`), a `*service.NoMethods` Net's `rcvrNone` (`noMethodsRcv`).

The decoding laws hold of bytes of the target's type only: `rpcDecode` panics (`rpcNotModelled`) on
a tag of another listed type, which Net's callers exclude (`bodyDecG`, `argDec`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Svc
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Defs
public import Net.Proof.net.rpc.Codec
public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.wire

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

/-- A pointer to a struct as an interface value. -/
abbrev ptrIface [GooseExts] [GoGlobalContext] (t : go.GoType) (p : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType t) #p

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [rpcdriver.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The codec's predicate transformers: the generated functions' weakest preconditions. -/
def drvCodec : net.rpc.CodecSpec GF where
  enc v Ψ := iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sl : GoSlice) (bs : List w8), sl ↦* bs -∗ ownSliceCap w8 sl (DFrac.own 1) -∗ Ψ bs -∗
        Φ #sl) -∗
    WP (App (Val #(functions rpcEncode [])) (Val #v)) {{ Φ }})
  dec bs ptr Ψ := iprop(∀ (data : GoSlice) (dq : DFrac) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else net.rpc.decErr err) -∗ Φ #err) -∗
    WP (App (App (Val #(functions rpcDecode [])) (Val #data)) (Val #ptr)) {{ Φ }})
  rcv rcvr Ψ := iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
    WP (App (Val #(functions rpcReceiver [])) (Val #rcvr)) {{ Φ }})

theorem drvCodec_encOk :
    ⊢ net.rpc.encOk (hG := hG) drvCodec (functions rpcEncode []) := by
  unfold net.rpc.encOk
  iintro !> %v %Ψ %Φ Henc HΦ
  unfold drvCodec
  iapply Henc
  iexact HΦ

theorem drvCodec_rcvOk :
    ⊢ net.rpc.rcvOk (hG := hG) drvCodec (functions rpcReceiver []) := by
  unfold net.rpc.rcvOk
  iintro !> %rcvr %Ψ %Φ Hr HΦ
  unfold drvCodec
  iapply Hr
  iexact HΦ

theorem drvCodec_decOk :
    ⊢ net.rpc.decOk (hG := hG) drvCodec (functions rpcDecode []) := by
  unfold net.rpc.decOk
  iintro !> %data %dq %bs %ptr %Ψ %Φ Hd Hdec HΦ
  unfold drvCodec
  iapply Hdec $$ Hd
  iexact HΦ

theorem drvCodec_rcv_eq (rcvr : GoInterface) (Ψ : Loc → IProp GF) :
    drvCodec.rcv rcvr Ψ = iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
      WP (App (Val #(functions rpcReceiver [])) (Val #rcvr)) {{ Φ }}) := rfl

/-! ## The client: encoding a request, decoding a reply -/

/-- (a) Encoding the request `*service.Args{id, dsl, fail}`, `dsl` holding `data`. -/
abbrev enc_Args.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (id : w64) (dsl : GoSlice) (fail : GoString) (dqs : DFrac)
    (data : List w8) (Ψ : List w8 → IProp GF),
    p ↦{dq} service.Args.mk id dsl fail ∗ dsl ↦*{dqs} data ∗
      (p ↦{dq} service.Args.mk id dsl fail -∗ dsl ↦*{dqs} data -∗ Ψ (encArgs id data fail)) ⊢
    drvCodec.enc (ptrIface service.Args.ty p) Ψ

/-- (b) Decoding a reply `encReply id data runs` into the zero `service.Reply` (the client's
`&service.Reply{}`): it succeeds, with `data` in a fresh slice (`nil` if `data` is empty, which gob
does not send). -/
abbrev dec_Reply.spec : Prop :=
  ∀ (p : Loc) (id : w64) (data : List w8) (runs : w64) (Ψ : Bool → IProp GF),
    p ↦ service.Reply.mk (W64 0) slice.nil (W64 0) ∗
      (∀ dsl : GoSlice, p ↦ service.Reply.mk id dsl runs -∗ dsl ↦* data -∗ Ψ true) ⊢
    drvCodec.dec (encReply id data runs) (ptrIface service.Reply.ty p) Ψ

/-! ## The server's bindings: decoding the arguments, encoding the reply -/

/-- Decoding a request `encArgs id data fail` into `NewArg()`'s zero `service.Args`: it succeeds,
with `data` in a fresh slice; the bytes are in a slice, so below `2^63`. -/
abbrev decA_Args.spec : Prop :=
  ∀ (p : Loc) (id : w64) (data : List w8) (fail : GoString) (Ψ : Bool → IProp GF),
    p ↦ service.Args.mk (W64 0) slice.nil go!"" ∗
      (∀ dsl : GoSlice, ⌜(encArgs id data fail).length < 2 ^ 63⌝ -∗
        p ↦ service.Args.mk id dsl fail -∗ dsl ↦* data -∗ Ψ true) ⊢
    drvCodec.dec (encArgs id data fail) (ptrIface service.Args.ty p) Ψ

/-- Encoding the reply `*service.Reply{id, dsl, runs}`, `dsl` holding `data`. -/
abbrev enc_Reply.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (id : w64) (dsl : GoSlice) (runs : w64) (dqs : DFrac)
    (data : List w8) (Ψ : List w8 → IProp GF),
    p ↦{dq} service.Reply.mk id dsl runs ∗ dsl ↦*{dqs} data ∗
      (p ↦{dq} service.Reply.mk id dsl runs -∗ dsl ↦*{dqs} data -∗ Ψ (encReply id data runs)) ⊢
    drvCodec.enc (ptrIface service.Reply.ty p) Ψ

/-- The codec's laws (proved in `CodecProof.lean`: `drvCodecLaws`). -/
structure CodecLaws : Prop where
  enc_Args : enc_Args.spec (GF := GF)
  dec_Reply : dec_Reply.spec (GF := GF)
  decA_Args : decA_Args.spec (GF := GF)
  enc_Reply : enc_Reply.spec (GF := GF)

/-! ## The receivers -/

/-- (c) The service `s` as `rpc.Register(s)` takes it: the codec's `rcv` gives the receiver with
the `Svc` service's spec (`Svc.lean`'s `echoSvc`). -/
abbrev svcRcv.spec : Prop :=
  ∀ (γid : GName) (s : Loc), ⌜s ≠ null⌝ ∗ net.rpc.codecSet drvCodec ∗ service.isSvc γid s ⊢
    (drvCodec (GF := GF)).rcv (ptrIface service.Svc.ty s)
      (net.rpc.rcvrIs drvCodec (ptrIface service.Svc.ty s) (echoSvc γid) go!"Svc" false)

/-- (d) A `*service.NoMethods`: a receiver with no method. -/
abbrev noMethodsRcv.spec : Prop :=
  ∀ (p : Loc), (⌜p ≠ null⌝ : IProp GF) ⊢
    (drvCodec (GF := GF)).rcv (ptrIface service.NoMethods.ty p)
      (net.rpc.rcvrNone (GF := GF) go!"NoMethods")

end codec

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

end Perennial
