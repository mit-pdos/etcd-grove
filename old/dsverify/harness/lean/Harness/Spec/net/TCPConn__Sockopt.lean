/-
The socket-option setters on a `*TCPConn` (kits/rabia-net): `c.SetReadBuffer(n)` and
`c.SetWriteBuffer(n)` (`net.go`, promoted from `*conn`), `c.SetKeepAlive(b)` and
`c.SetKeepAlivePeriod(d)` (`tcpsock.go`). In the model (`TrustedCode/net.lean`,
`model.setSockopt`) each may fail, on any end (Go's `setsockopt` fails for a closed end, and
otherwise only rarely; the model over-approximates), and changes nothing else. Needs only the end
(`ownTCPConn`, persistent). The error is `nil` exactly on success, an `*OpError` of `"set"`
otherwise (`connErr`; for a closed end, the one `net.ErrClosed` holds). Proved in
`Proof/net/TCPConn__Sockopt.lean`.
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
abbrev net.TCPConn.SetReadBuffer.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"SetReadBuffer")) (Val #n))
  {{ (err : GoInterface), RET #err; ∃ code : w64,
      ⌜err = interface.nil ↔ code = errNone⌝ ∗ net.connErr go!"set" code err }}

/-- See the file header. -/
abbrev net.TCPConn.SetWriteBuffer.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"SetWriteBuffer")) (Val #n))
  {{ (err : GoInterface), RET #err; ∃ code : w64,
      ⌜err = interface.nil ↔ code = errNone⌝ ∗ net.connErr go!"set" code err }}

/-- See the file header. -/
abbrev net.TCPConn.SetKeepAlive.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"SetKeepAlive")) (Val #b))
  {{ (err : GoInterface), RET #err; ∃ code : w64,
      ⌜err = interface.nil ↔ code = errNone⌝ ∗ net.connErr go!"set" code err }}

/-- See the file header. -/
abbrev net.TCPConn.SetKeepAlivePeriod.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"SetKeepAlivePeriod")) (Val #d))
  {{ (err : GoInterface), RET #err; ∃ code : w64,
      ⌜err = interface.nil ↔ code = errNone⌝ ∗ net.connErr go!"set" code err }}

end spec

end Perennial
