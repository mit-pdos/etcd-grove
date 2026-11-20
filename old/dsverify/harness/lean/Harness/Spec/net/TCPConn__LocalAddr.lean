/-
`c.LocalAddr()` on a `*TCPConn` (`net.go`, promoted from `*conn`): in the model
(`TrustedCode/net.lean`, `conn.LocalAddr.impl`), `c.fd.laddr`, an arbitrary `*TCPAddr` fixed
when the connection was made (by `Dial` or `Accept`). The spec says that it returns (no panic)
a non-`nil` `*TCPAddr` (`net.isTCPAddr`), whose `String()` returns some string
(`net.wp_Addr_String`; `net.TCPConn.LocalAddr.wp_String` for `c.LocalAddr().String()`). Proved in
`Proof/net/TCPConn__LocalAddr.lean`.
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
abbrev net.TCPConn.LocalAddr.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool),
  {{ net.ownTCPConn (GF := GF) c cid side }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"LocalAddr")) (Val #()))
  {{ (ad : GoInterface), RET #ad; ⌜net.isTCPAddr ad⌝ }}

end spec

end Perennial
