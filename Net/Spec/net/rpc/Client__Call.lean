/-
`c.Call(sm, args, reply)` (`client.go`; dsverify-lab's `Client.Call.spec`,
`Harness/Proof/net/rpc/ClientDefs.lean`): `nil` after one run of the method at the server on the
encoded arguments, with the reply `rep` decoded into `reply` (`Θ rep true`). The decoding
obligation `□ (D -∗ ∀ rep, Φ rep "" -∗ C.dec rep reply (Θ rep))` is asked only of the replies the
method answers with, its answer `Φ rep ""` in hand (it goes to the decoding: `Θ` keeps of it what
the caller needs): a generated codec decodes only bytes of the reply's type (on a value of another
listed type its `Decode` panics, `rpcNotModelled`), and it is the method's spec that says its
replies are of that type;
`ServerError(msg)` for a non-empty `msg` after one run, with its answer `Φ rep msg` and the
decoding resource `D` back; or another error, which is not a `ServerError`, after at most one run
(the deposit is lost), with `D` back or a failed decoding, or, when nothing was encoded (the
client was shut down or closing, or an earlier write failed), the encoding premise and `D` back.
Every error comes with its `Error()` (`errMsg` for a `ServerError`; `errAny` for the others, whose
message may be arbitrary: the net extension's `*OpError`). The service is one the address offers
with the spec `S` (`splitSM sm`), and `reply` is not `nil` (Go's `Call` with a `nil` reply discards
the reply; not specified). The request fits the frames the model's server reads (`maxFrameN`, 1 GiB):
the service method (`sm.length + 16 ≤ maxFrameN`) and the arguments' encoding, whose continuation
carries the bound (`⌜bs.length ≤ maxFrameN⌝`), which the caller proves of its own encoding (a longer
frame is the model's stuck point: `clientCodec.WriteRequest.spec`). Proved in
`Net/Proof/net/rpc/Client__Call.lean`.
-/
module

public import Net.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Client.Call.spec : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a sm svc M : GoString) (S : MethodSpec GF)
    (args reply : GoInterface) (Φ : List w8 → GoString → IProp GF) (Rargs D : IProp GF)
    (Θ : List w8 → Bool → IProp GF) (C : CodecSpec GF),
  {{ isClient c W a ∗ ⌜splitSM sm = some (svc, M) ∧ W.SS a svc = some S ∧ reply ≠ interface.nil⌝ ∗
      ⌜sm.length + 16 ≤ maxFrameN⌝ ∗ codecSet C ∗ C.enc args (fun bs => iprop(⌜bs.length ≤ maxFrameN⌝ ∗ S M bs Φ ∗ Rargs)) ∗ D ∗
      □ (D -∗ ∀ rep, Φ rep [] -∗ C.dec rep reply (Θ rep)) }}
    (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
      (Val #sm)) (Val #args)) (Val #reply))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ Rargs ∗ ∃ rep, Θ rep true) ∨
      (∃ msg : GoString, ⌜msg ≠ [] ∧ err = serverErr msg⌝ ∗ errMsg err msg ∗ Rargs ∗
        (∃ rep, Φ rep msg) ∗ D) ∨
      (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ models_lab.errAny err ∗
        ((Rargs ∗ (D ∨ ∃ rep, Θ rep false)) ∨
          (C.enc args (fun bs => iprop(⌜bs.length ≤ maxFrameN⌝ ∗ S M bs Φ ∗ Rargs)) ∗ D))) }}

end spec

end net.rpc
end Perennial
