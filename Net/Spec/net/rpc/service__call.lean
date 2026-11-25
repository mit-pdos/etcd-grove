/-
`svc.call(server, sending, wg, mtype, req, argv, replyv, codec)` (`server.go`), a request's run on
the model's server codec `sc` of the acceptor's end of `cn`: it counts the call (`mtype`'s mutex),
runs the method on the request's argument (`callReady`: the call of the registered `Method`, which
answers the continuation `Φ`, `callRet`), answers request `k` with its result (`sendResponse`: the
error's message, or the reply's encoding) and frees `req`; `wg.Done()` (deferred) by the thread-token
join of the request loop (`sync.tokJoin`, at `srvWgN`), whose slot's thread token it exits with.
Proved in `Net/Proof/net/rpc/service__call.lean`.
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
variable [π : NetProtoGS] [sync.Assumptions]

/-- See the file header. -/
abbrev service.call.spec : Prop :=
  ∀ (svc s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) (sc t : Loc)
    (cn : Nat) (la ra : GoInterface) (sending wg mt req : Loc) (rqv : net.rpc.Request)
    (argv replyv : GoInterface) (k : Nat) (Φ : List w8 → GoString → IProp GF),
  {{ isServerAny s γs ∗ srvEnv ∗ codecSet C ∗ srvCodecAt sc t cn a la ra ∗
      sync.isMutex sending (srvSendInv W a cn sc) ∗ req ↦ rqv ∗ ⌜rqv.Seq' = W64 k ∧ wg ≠ null⌝ ∗
      ansPend W a cn k rqv.ServiceMethod' Φ ∗ callReady C svc mt argv replyv Φ ∗
      sync.tokJoin.ownDone srvWgN iprop(False) wg iprop(True) }}
    (App (App (App (App (App (App (App (App
      (Val (svc @!! go.GoType.PointerType net.rpc.service.ty @!! go!"call"))
      (Val #s)) (Val #sending)) (Val #wg)) (Val #mt)) (Val #req)) (Val #argv)) (Val #replyv))
      (Val #(interface.mkOk (go.GoType.PointerType net.rpc.serverCodec.ty) #sc)))
  {{ RET #(); threadTok }}

end spec

end net.rpc
end Perennial
