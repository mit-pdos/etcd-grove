/-
`server.ServeConn(conn)` (`server.go`) on the acceptor's end `t` of a connection `cn` just accepted
at `a` (`rpcAccepted`): `ServeCodec` (`Server.ServeCodec.spec`) on a new server codec over it
(`newServerCodec`). Proved in `Net/Proof/net/rpc/Server__ServeConn.lean`.
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
abbrev Server.ServeConn.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) (t : Loc)
    (cn : Nat) (la ra : GoInterface),
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServer s γs ∗ srvServes γs C W a ∗ srvEnv ∗ codecSet C ∗
      net.connAt (GF := GF) t cn true a la ra ∗ rpcAccepted W a cn ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"ServeConn"))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t)))
  {{ RET #(); threadTok }}

end spec

end net.rpc
end Perennial
