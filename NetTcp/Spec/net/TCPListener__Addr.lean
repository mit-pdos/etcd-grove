/-
D18. `li.Addr()` on a `Listener` `li` that is this node's listener `l` (`isListener`: a `*TCPListener`
`t` with `lisAt t l x`), stated on the resolved method (`TCPListener.Addr.impl`,
`NetTcp/TrustedCode/net.lean`): `x`, the same non-nil `*TCPAddr` at every call (`lisAt`'s
`tcpAddr x`), before and after `Close`. Proved in `NetTcp/Proof/net/TCPListener__Addr.lean`.
-/
module

public import NetTcp.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Tcp

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev TCPListener.Addr.spec : Prop :=
  ∀ (t : Loc) (l : w64) (x : GoInterface),
  {{ lisAt (GF := GF) t l x }}
    (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"Addr" #t)) (Val #()))
  {{ RET #x; True }}

end spec

end net
end Perennial
