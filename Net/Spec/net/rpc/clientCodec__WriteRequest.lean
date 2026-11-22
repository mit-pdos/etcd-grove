/-
`c.WriteRequest(r, body)` on the model's client codec `c` (`codec.go`), whose `rwc` holds the end
`s` of the connection `cn` (kept, `↦□`) and whose sticky write error `werr` the caller owns (`w0`):
with `w0` not `nil` it returns `w0` and does nothing else; otherwise it encodes `body` with the
registered codec (`codecSet C`; `C.enc body Ψ0`, whose bytes are `eb`), and writes the request,
`reqWire seq sm eb` (`r`'s `Seq` and `ServiceMethod`: a header frame and a body frame), in one
`Write`.

The writer is the library's (`GooseLang/Ext/Net/Proto.lean`): the caller has written `W0` with the
protocol `Pr` (`sendTok`), and its update `reqUpd` turns the encoding's `Ψ0 eb` into the protocol
fact of what it will have written (`□ Pr cn (W0 ++ reqWire seq sm eb)`) and its own `Ψ eb`: the
place where a caller records the request it is about to send. It
returns `nil` with the whole request written, or the `Write`'s error (`resErr`, an `*OpError`), the
request written only in part (`w`, a strict prefix), which `werr` then holds.
Proved in `Net/Proof/net/rpc/clientCodec__WriteRequest.lean`.
-/
module

public import Net.Proof.net.rpc.Codec
public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- What the caller of `WriteRequest` gives for the bytes `eb` of the encoding (whose
continuation is `Ψ0`), knowing that the request's payloads fit their frames: the protocol fact of
everything written once the request is, and its own `Ψ eb`. -/
def reqUpd (cn : Nat) (Pr : Proto GF) (W0 : List w8) (seq : w64) (sm : GoString)
    (Ψ0 Ψ : List w8 → IProp GF) : IProp GF :=
  iprop(∀ eb, ⌜sm.length + 16 < 2 ^ 63 ∧ eb.length < 2 ^ 63⌝ -∗ Ψ0 eb ={⊤}=∗
    □ Pr cn (W0 ++ reqWire seq sm eb) ∗ Ψ eb)

/-- See the file header. -/
abbrev clientCodec.WriteRequest.spec : Prop :=
  ∀ (c t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (r : Loc)
    (rv : net.rpc.Request) (body w0 ed : GoInterface) (C : CodecSpec GF) (Pr : Proto GF)
    (W0 : List w8) (Ψ0 Ψ : List w8 → IProp GF),
  {{ structFieldRef net.rpc.clientCodec go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      net.connAt (GF := GF) t cn s a la ra ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      structFieldRef net.rpc.clientCodec go!"werr" c ↦ w0 ∗ r ↦ rv ∗ codecSet C ∗
      sendTok (Gg := hG.goose_globalGS) cn s Pr W0 ∗
      C.enc body Ψ0 ∗ reqUpd cn Pr W0 rv.Seq' rv.ServiceMethod' Ψ0 Ψ }}
    (App (App (Val (c @!! go.GoType.PointerType net.rpc.clientCodec.ty @!! go!"WriteRequest"))
      (Val #r)) (Val #body))
  {{ (err : GoInterface), RET #err; r ↦ rv ∗
      ((⌜w0 ≠ interface.nil ∧ err = w0⌝ ∗ structFieldRef net.rpc.clientCodec go!"werr" c ↦ w0 ∗
          sendTok (Gg := hG.goose_globalGS) cn s Pr W0 ∗
          C.enc body Ψ0 ∗ reqUpd cn Pr W0 rv.Seq' rv.ServiceMethod' Ψ0 Ψ) ∨
        (⌜w0 = interface.nil⌝ ∗ ∃ eb, Ψ eb ∗
          ((⌜err = interface.nil⌝ ∗ structFieldRef net.rpc.clientCodec go!"werr" c ↦ err ∗
              sendTok (Gg := hG.goose_globalGS) cn s Pr
                (W0 ++ reqWire rv.Seq' rv.ServiceMethod' eb)) ∨
            (∃ (w : List w8) (k : NetErr),
              ⌜w <+: reqWire rv.Seq' rv.ServiceMethod' eb ∧
                w ≠ reqWire rv.Seq' rv.ServiceMethod' eb⌝ ∗
              structFieldRef net.rpc.clientCodec go!"werr" c ↦ err ∗
              sendTok (Gg := hG.goose_globalGS) cn s Pr (W0 ++ w) ∗
              net.resErr (some k) go!"write" la ra (some ed) (· = go!"write") err)))) }}

end spec

end net.rpc
end Perennial
