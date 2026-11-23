/-
`server.readRequest(codec)` (`server.go`), by the request loop of a connection served at `a` (as
`readRequestHeader.spec`): the header (`readRequestHeader`), then the body:

* the header's read failed: `keepReading` is `false` with an error;
* otherwise request `k` (`req`, its sequence number `k`) was taken, with the right to answer it
  once (`ansPend`), and the reader is back at the top of its loop (`rdrOwn`, the body read or the
  read failed); `keepReading` is `true`, and either `nil` with the request ready to run
  (`callReady`: the method's argument `argv` decoded from the request's argument bytes and its
  reply `replyv` made, by the method's `NewArg` and `NewReply`), or an error with a message not
  empty (the method is not registered, or the body did not read or decode) and the continuation's
  error answers (`errCont`).

Proved in `Net/Proof/net/rpc/Server__readRequest.lean`.
-/
module

public import Net.Proof.net.rpc.ServerDefs

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
abbrev Server.readRequest.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) (sc t : Loc)
    (cn : Nat) (la ra : GoInterface),
  {{ isServer s γs ∗ srvServes γs C W a ∗ srvEnv ∗ srvCodecAt sc t cn a la ra ∗
      rdrOwn W a cn sc }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"readRequest"))
      (Val #(interface.mkOk (go.GoType.PointerType net.rpc.serverCodec.ty) #sc)))
  {{ (svc mt req : Loc) (argv replyv : GoInterface) (keep : Bool) (err : GoInterface),
      RET (PairV (PairV (PairV (PairV (PairV (PairV #svc #mt) #req) #argv) #replyv) #keep) #err);
      ⌜keep = false ∧ err ≠ interface.nil⌝ ∨
      (⌜keep = true⌝ ∗ ∃ (k : Nat) (r : RpcReq) (Φ : List w8 → GoString → IProp GF),
        req ↦ { (_root_.Perennial.zero_val net.rpc.Request) with ServiceMethod' := r.sm, Seq' := W64 k } ∗
        ansPend W a cn k r.sm Φ ∗ rdrOwn W a cn sc ∗
        ((⌜err = interface.nil⌝ ∗ callReady C svc mt argv replyv Φ) ∨
          (⌜err ≠ interface.nil⌝ ∗ errNE err ∗ errCont Φ))) }}

end spec

end net.rpc
end Perennial
