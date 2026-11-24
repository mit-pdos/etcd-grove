/-
`server.ServeCodec(codec)` (`server.go`) on the model's server codec `sc` of a connection `cn`
just accepted at `a` (`srvCodecOwn`: no write or read error, not closed, the acceptor's tokens),
on a server whose registrations serve `a` (`srvServes`) with a registered codec meeting `C`: it
reads the connection's requests in order, each a client's (the `k`-th has the sequence number
`k`) and taken once, its deposit with it; a request ready to run (`callReady`) runs in a goroutine
of its own (`service.call`, counted by the wait group: Perennial's thread-token join,
`sync.tokJoin`, the reader's thread token deposited at each `Add`), any other is answered with its
error at once (`sendResponse`); every response under `sending` (`srvSendInv`), in the protocol's
wire order. Once a header's read fails it waits for the runs and closes the codec. The caller's
thread token comes back; the wait group's counter is bounded by the goroutines alive
(`threadBound GF ≤ 2 ^ 31`). Proved in `Net/Proof/net/rpc/Server__ServeCodec.lean`.
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
abbrev Server.ServeCodec.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) (sc t : Loc)
    (cn : Nat) (la ra : GoInterface),
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServer s γs ∗ srvServes γs C W a ∗ srvEnv ∗ codecSet C ∗
      srvCodecAt sc t cn a la ra ∗ srvCodecOwn W a cn sc ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"ServeCodec"))
      (Val #(interface.mkOk (go.GoType.PointerType net.rpc.serverCodec.ty) #sc)))
  {{ RET #(); threadTok }}

end spec

end net.rpc
end Perennial
