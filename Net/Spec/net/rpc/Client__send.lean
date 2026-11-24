/-
`c.send(call)` (`client.go`) on a `*Call` `pc` that `Go` filled in, with its ticket `γt` (unwritten)
and its promise (`callDone`): under `reqMutex`, it numbers the call under `mutex` (or, if the
client is shut down or closing, fails it with `ErrShutdown`), records it in `pending`, and writes
its request (`WriteRequest`: the codec's encoding of `args`, whose continuation's deposit `S M bs Φ`
goes to the connection, `reqProto`), failing the call with the write's error if the write fails and
the call is still pending. It writes the call's number on its ticket, and returns `sendRes`: the
encoding's `Rargs`, or, nothing encoded, the encoding premise back with the request unsent. Proved
in `Net/Proof/net/rpc/Client__send.lean`.
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
abbrev Client.send.spec : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a : GoString) (γ : ClientNames) (pc : Loc) (sm svc M : GoString)
    (S : MethodSpec GF) (args reply : GoInterface) (ch : Loc) (γt : GName) (γf : FutureNames)
    (K : Loc → IProp GF) (Φ : List w8 → GoString → IProp GF) (Rargs D : IProp GF)
    (Θ : List w8 → Bool → IProp GF) (C : CodecSpec GF),
  {{ isClientN c W a γ ∗
      ⌜splitSM sm = some (svc, M) ∧ W.SS a svc = some S ∧ reply ≠ interface.nil ∧ pc ≠ null⌝ ∗
      ⌜sm.length + 16 ≤ maxFrameN⌝ ∗ codecSet C ∗ C.enc args (fun bs => iprop(⌜bs.length ≤ maxFrameN⌝ ∗ S M bs Φ ∗ Rargs)) ∗ D ∗
      □ (D -∗ ∀ rep, Φ rep [] -∗ C.dec rep reply (Θ rep)) ∗
      ghostMapAuth γt 1 (∅ : GMap Unit (Option Nat)) ∗
      callFields pc sm args reply ch ∗ structFieldRef net.rpc.Call go!"Error" pc ↦ interface.nil ∗
      callDone γ.conn γt sm args reply ch γf K Φ Θ D }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"send")) (Val #pc))
  {{ RET #(); ∃ o, ticket γt o ∗
      sendRes γ.conn o Rargs (C.enc args (fun bs => iprop(⌜bs.length ≤ maxFrameN⌝ ∗ S M bs Φ ∗ Rargs))) }}

end spec

end net.rpc
end Perennial
