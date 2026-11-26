/-
`NewClientWithCodec(codec)` on the model's client codec `cc` (`newClientCodec`'s: its `rwc` the
dialer's end of `cn`, no write error yet) over a connection just dialed to `a` and registered in
`W` (`rpcDialed`): a client of `a` in `W`, its reader `input` forked. The premise
`receiptBound GF ≤ 2 ^ 64` (the adequacy theorem's choice of the step bound) is what makes the
client's sequence numbers distinct (`ClientDefs.lean`). Proved in
`Net/Proof/net/rpc/NewClientWithCodec.lean`.
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
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev NewClientWithCodec.spec : Prop :=
  ∀ (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (cc t : Loc)
    (la ra : GoInterface),
  {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗
      structFieldRef net.rpc.clientCodec go!"rwc" cc ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      structFieldRef net.rpc.clientCodec go!"werr" cc ↦ interface.nil ∗
      net.connAt (GF := GF) t cn false a la ra ∗ rpcDialed W a cn γ }}
    (App (Val (@! net.rpc.NewClientWithCodec))
      (Val #(interface.mkOk (go.GoType.PointerType net.rpc.clientCodec.ty) #cc)))
  {{ (c : Loc), RET #c; isClient c W a }}

end spec

end net.rpc
end Perennial
