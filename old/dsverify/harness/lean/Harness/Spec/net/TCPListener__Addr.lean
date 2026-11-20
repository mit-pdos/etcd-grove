/-
`l.Addr()` on a `*TCPListener` (`tcpsock.go`): in the model (`TrustedCode/net.lean`,
`TCPListener.Addr.impl`), the listener's local address `l.fd.laddr`, an arbitrary `*TCPAddr`
fixed when the listener was made. The spec says only that it returns (no panic). Proved in
`Proof/net/TCPListener__Addr.lean`, which also gives, from the persistent `ownListener` alone,
that the address is a non-`nil` `*TCPAddr` (`net.TCPListener.Addr.wp_TCPAddr`), the spec of
`l.Addr().String()` (`net.TCPListener.Addr.wp_String`: some string), and both through the
`net.Listener` interface (`net.wp_Listener_Addr`, `net.wp_Listener_Addr_String`). The address
is not tied to the listened-on `a` (for a wildcard `Listen`, Go reports `"[::]:port"`;
`TrustedCode/net.lean`).
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
abbrev net.TCPListener.Addr.spec : Prop :=
  ∀ (l : Loc) (lid : w64) (a : GoString),
  {{ net.ownListener (GF := GF) l lid a }}
    (App (Val (l @!! go.GoType.PointerType net.TCPListener.ty @!! go!"Addr")) (Val #()))
  {{ (ad : GoInterface), RET #ad; True }}

end spec

end Perennial
