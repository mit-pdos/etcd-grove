/-
`c.WriteResponse(r, body)` on the model's server codec `c` (`codec.go`), whose `rwc` holds the end
`s` of the connection `cn` (kept, `↦□`) and whose sticky write error `werr` the caller owns (`w0`):
with `w0` not `nil` it returns `w0` and does nothing else; otherwise it writes the response,
`respWire seq sm e eb` (`r`'s `Seq`, `ServiceMethod` and `Error`: a header frame and a body frame),
in one `Write`. The body frame of a success response (`e = ""`) is the registered codec's encoding
`eb` of `body` (`codecSet C`; the caller's `C.enc body Ψ0`), of an error response empty (`body` is
not encoded: the caller gives `Ψ0 []` instead, `respEnc`).
The writer is the library's (`GooseLang/Ext/Net/Proto.lean`), as in `clientCodec.WriteRequest.spec`:
the caller has written `W0` with the protocol `Pr` (`sendTok`), and its update `respUpd` (needed
only without a write error) turns `Ψ0 eb` into the protocol fact of what it will have written and
its own `Ψ eb`. It returns `nil` with the whole response written, or the `Write`'s error (`resErr`,
an `*OpError`), the response written only in part (`w`, a strict prefix), which `werr` then holds.
Proved in `Net/Proof/net/rpc/serverCodec__WriteResponse.lean`.
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

/-- What the caller of `WriteResponse` gives for the bytes `eb` of the body (whose continuation is
`Ψ0`), knowing that the response's payloads fit their frames: the protocol fact of everything
written once the response is, and its own `Ψ eb`. -/
def respUpd (cn : Nat) (Pr : Proto GF) (W0 : List w8) (seq : w64) (sm e : GoString)
    (Ψ0 Ψ : List w8 → IProp GF) : IProp GF :=
  iprop(∀ eb, ⌜sm.length + e.length + 24 < 2 ^ 63 ∧ eb.length < 2 ^ 63⌝ -∗ Ψ0 eb ={⊤}=∗
    □ Pr cn (W0 ++ respWire seq sm e eb) ∗ Ψ eb)

/-- The body's premise: its encoding for a success response (`e = ""`), `Ψ0 []` for an error
response (nothing is encoded). -/
def respEnc (C : CodecSpec GF) (e : GoString) (body : GoInterface) (Ψ0 : List w8 → IProp GF) :
    IProp GF :=
  if e = [] then C.enc body Ψ0 else Ψ0 []

/-- See the file header. -/
abbrev serverCodec.WriteResponse.spec : Prop :=
  ∀ (c t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (r : Loc)
    (rv : net.rpc.Response) (body w0 ed : GoInterface) (C : CodecSpec GF) (Pr : Proto GF)
    (W0 : List w8) (Ψ0 Ψ : List w8 → IProp GF),
  {{ structFieldRef net.rpc.serverCodec go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      net.connAt (GF := GF) t cn s a la ra ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      structFieldRef net.rpc.serverCodec go!"werr" c ↦ w0 ∗ r ↦ rv ∗ codecSet C ∗
      sendTok (Gg := hG.goose_globalGS) cn s Pr W0 ∗
      respEnc C rv.Error' body Ψ0 ∗
      (⌜w0 = interface.nil⌝ -∗ respUpd cn Pr W0 rv.Seq' rv.ServiceMethod' rv.Error' Ψ0 Ψ) }}
    (App (App (Val (c @!! go.GoType.PointerType net.rpc.serverCodec.ty @!! go!"WriteResponse"))
      (Val #r)) (Val #body))
  {{ (err : GoInterface), RET #err; r ↦ rv ∗
      ((⌜w0 ≠ interface.nil ∧ err = w0⌝ ∗ structFieldRef net.rpc.serverCodec go!"werr" c ↦ w0 ∗
          sendTok (Gg := hG.goose_globalGS) cn s Pr W0 ∗ respEnc C rv.Error' body Ψ0) ∨
        (⌜w0 = interface.nil⌝ ∗ ∃ eb, Ψ eb ∗
          ((⌜err = interface.nil⌝ ∗ structFieldRef net.rpc.serverCodec go!"werr" c ↦ err ∗
              sendTok (Gg := hG.goose_globalGS) cn s Pr
                (W0 ++ respWire rv.Seq' rv.ServiceMethod' rv.Error' eb)) ∨
            (∃ (w : List w8) (k : NetErr),
              ⌜w <+: respWire rv.Seq' rv.ServiceMethod' rv.Error' eb ∧
                w ≠ respWire rv.Seq' rv.ServiceMethod' rv.Error' eb⌝ ∗
              structFieldRef net.rpc.serverCodec go!"werr" c ↦ err ∗
              sendTok (Gg := hG.goose_globalGS) cn s Pr (W0 ++ w) ∗
              net.resErr (some k) go!"write" la ra (some ed) (· = go!"write") err)))) }}

end spec

end net.rpc
end Perennial
