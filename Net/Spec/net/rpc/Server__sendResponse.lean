/-
`server.sendResponse(sending, req, reply, codec, errmsg)` (`server.go`), on the model's server codec
`sc` of the acceptor's end of `cn` (`srvCodecAt`), with `sending` the connection's write lock
(`srvSendInv`): it answers request `k` of the connection (`req`'s `Seq` is `k`), once (`ansPend`),
with the message `errmsg` (`""` for a success) and, for a success, `reply`'s encoding (`ansRes`):
under `sending`, the response is written, its answer recorded with the continuation's
`Φ reply msg` for the client; or, once a write failed, nothing is written. `req` is only read.
Proved in `Net/Proof/net/rpc/Server__sendResponse.lean`.
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
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.sendResponse.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) (sc t : Loc)
    (cn : Nat) (la ra : GoInterface) (sending req : Loc) (rqv : net.rpc.Request)
    (reply : GoInterface) (errmsg : GoString) (k : Nat) (Φ : List w8 → GoString → IProp GF),
  {{ isServer s γs ∗ srvEnv ∗ codecSet C ∗ srvCodecAt sc t cn a la ra ∗
      sync.isMutex sending (srvSendInv W a cn sc) ∗ req ↦ rqv ∗ ⌜rqv.Seq' = W64 k⌝ ∗
      ansPend W a cn k rqv.ServiceMethod' Φ ∗ ansRes C errmsg reply Φ }}
    (App (App (App (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"sendResponse"))
      (Val #sending)) (Val #req)) (Val #reply))
      (Val #(interface.mkOk (go.GoType.PointerType net.rpc.serverCodec.ty) #sc))) (Val #errmsg))
  {{ RET #(); req ↦ rqv }}

end spec

end net.rpc
end Perennial
