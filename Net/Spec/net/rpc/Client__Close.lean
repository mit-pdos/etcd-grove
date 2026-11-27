/-
`c.Close()` on an rpc client (`client.go`): under `mutex`, `ErrShutdown` if it was closed already,
else `closing` is set and the codec's `Close` closes the connection (any of the connection's
outcomes: the library's `close_au`). An error comes with its `Error()` (`errAny`). Proved in
`Net/Proof/net/rpc/Client__Close.lean`.
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
abbrev Client.Close.spec : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a : GoString),
  {{ isClient c W a }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∨ models_lab.errAny err }}

/-- `Client.Close.spec`, which also says the client is closing for good afterwards (`cliClosed`:
whichever branch ran, `closing` is set). Proved in `Net/Proof/net/rpc/Client__CloseClosed.lean`. -/
abbrev Client.Close.spec_closed : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a : GoString),
  {{ isClient c W a }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; (⌜err = interface.nil⌝ ∨ models_lab.errAny err) ∗ cliClosed c }}

end spec

end net.rpc
end Perennial
