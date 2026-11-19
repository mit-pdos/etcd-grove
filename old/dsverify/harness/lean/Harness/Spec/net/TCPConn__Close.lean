/-
`c.Close()` on a `*TCPConn` (`net.go`, promoted from `*conn`): in the model
(`TrustedCode/net.lean`, `conn.Close.impl`), the extension's `Close` of the end. Needs only
the end (`ownTCPConn`, persistent): no token changes (a closed end's later operations fail).
The error is `nil` exactly on success, an `*OpError` of `"close"` otherwise (`connErr`; a second
`Close` fails, with the model's `ErrNetClosing` inside, so that `errors.Is(err,
net.ErrClosed)`). Proved in `Proof/net/TCPConn__Close.lean`.
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
abbrev net.TCPConn.Close.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ code : w64,
      ⌜err = interface.nil ↔ code = errNone⌝ ∗ net.connErr go!"close" code err }}

end spec

end Perennial
