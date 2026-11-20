/-
`l.Close()` on a `*TCPListener` (`tcpsock.go`): in the model (`TrustedCode/net.lean`,
`TCPListener.Close.impl`), the extension's `CloseListener`. Needs only the listener
(`ownListener`, persistent); the address's token, if the caller holds it, stays the caller's.
Returns `nil` or an `*OpError` of `"close"` (`opResult`; a second `Close` fails, with the
model's `ErrNetClosing` inside). Proved in `Proof/net/TCPListener__Close.lean`.
-/
module

public import Harness.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI NetConn

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

/-- See the file header. -/
abbrev net.TCPListener.Close.spec : Prop :=
  ∀ (l : Loc) (lid : w64) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownListener (GF := GF) l lid a }}
    (App (Val (l @!! go.GoType.PointerType net.TCPListener.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ code : w64, net.opResult go!"close" code err }}

end spec

end Perennial
