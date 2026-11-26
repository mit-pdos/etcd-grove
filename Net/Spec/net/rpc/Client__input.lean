/-
`c.input()`, the client's reader goroutine (`client.go`): it reads responses until a read fails,
each answering the pending call its sequence number names (removed from `pending` first, so a call
is answered at most once: `ServerError(msg)` with the method's answer for an error response, the
reply decoded with the method's answer otherwise), or discarded if there is none; then it shuts the
client down and fails every pending call with the error (`ErrShutdown` or `io.ErrUnexpectedEOF`
for an `io.EOF`, as the client was closing or not). It needs the reader's resources (`readerOwn`:
what it has read, and that the client is not shut down) and returns nothing. Proved in
`Net/Proof/net/rpc/Client__input.lean`.
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
abbrev Client.input.spec : Prop :=
  ∀ (c : Loc) (W : RpcWorld GF) (a : GoString) (γ : ClientNames) (cc t : Loc) (cn : Nat)
    (la ra : GoInterface),
  {{ clientAt c W a γ cc t cn la ra ∗ readerOwn γ cn W a }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"input")) (Val #()))
  {{ RET #(); True }}

end spec

end net.rpc
end Perennial
