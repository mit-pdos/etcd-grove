/-
`c.SetWriteDeadline(t)` on a `*TCPConn` (`net.go`, promoted from `*conn`): in the model
(`TrustedCode/net.lean`, `conn.SetWriteDeadline.impl`), the extension's `SetDeadline` of the
write deadline (set unless `t` is the zero `time.Time`; time is not modeled, so any later
operation with a deadline set may time out). Needs only the end (`ownTCPConn`, persistent). The
error is `nil` exactly on success, an `*OpError` of `"set"` otherwise (`connErr`). Proved in
`Proof/net/TCPConn__SetWriteDeadline.lean`.
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
abbrev net.TCPConn.SetWriteDeadline.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool) (t : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"SetWriteDeadline")) (Val #t))
  {{ (err : GoInterface), RET #err; ∃ code : w64,
      ⌜err = interface.nil ↔ code = errNone⌝ ∗ net.connErr go!"set" code err }}

end spec

end Perennial
