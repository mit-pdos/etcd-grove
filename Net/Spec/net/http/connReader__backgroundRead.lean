/-
`cr.backgroundRead()` (the model's `server.go`), the goroutine `startBackgroundRead` forks: on the
connection reader `cr` (`crIs`) of the acceptor's end of `cn` (`connAt`, `cr.rwc` its `*TCPConn`),
with the background reader's token, the byte buffer and the reader's token at the head `hs`, one
`Read` of a byte; then, under the mutex, the byte kept (`hasByte`, with `Z cn`: the dialer wrote past
its head, `headLaw`), or an error but the abort's timeout recorded (`failed`, the connection's
context canceled and its current response notified, `crConnOk`), and the tokens, the buffer and the
reader's token given back to the invariant (`inRead` false), and the condition variable broadcast.
Proved in `Net/Proof/net/http/connReader__backgroundRead.lean`.
-/
module

public import Net.Proof.net.http.ConnReader
public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev connReader.backgroundRead.spec : Prop :=
  ∀ (cr : Loc) (γ : CrNames) (t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface)
    (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) (arr : GoArray w8 1),
  {{ crIs cr γ cn P hs Z ∗ headLaw P hs Z ∗ readEnv ∗
      structFieldRef net.http.connReader go!"rwc" cr ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      connAt t cn true a la ra ∗ token γ.bg ∗
      structFieldRef net.http.connReader go!"byteBuf" cr ↦ arr ∗
      recvTok (Gg := hG.goose_globalGS) cn true P hs }}
    (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"backgroundRead"))
      (Val #()))
  {{ RET #(); True }}

end spec

end net.http
end Perennial
