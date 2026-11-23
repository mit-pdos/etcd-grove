/-
`NewClient(conn)` on the dialer's end of a connection just dialed to `a` and registered in `W`
(`rpcDialed`), the `*TCPConn` `t`: a client of `a` in `W` over the model's frame codec
(`NewClientWithCodec(newClientCodec(conn))`). Proved in `Net/Proof/net/rpc/NewClient.lean`.
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
abbrev NewClient.spec : Prop :=
  ∀ (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (t : Loc)
    (la ra : GoInterface),
  {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ net.connAt (GF := GF) t cn false a la ra ∗
      rpcDialed W a cn γ }}
    (App (Val (@! net.rpc.NewClient))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t)))
  {{ (c : Loc), RET #c; isClient c W a }}

end spec

end net.rpc
end Perennial
