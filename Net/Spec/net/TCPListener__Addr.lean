/-
D18. `li.Addr()` on a `Listener` `li` that is this node's listener `l` (`isListener`: a `*TCPListener`
`t` with `lisAt t l x`), stated on the resolved method (`TCPListener.Addr.impl`,
`Net/TrustedCode/net.lean`): `x`, the same non-nil `*TCPAddr` at every call (`lisAt`'s
`netAddr x`), before and after `Close`. Proved in `Net/Proof/net/TCPListener__Addr.lean`.
-/
module

public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev TCPListener.Addr.spec : Prop :=
  ∀ (t : Loc) (l : w64) (x : GoInterface),
  {{ lisAt (GF := GF) t l x }}
    (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"Addr" #t)) (Val #()))
  {{ RET #x; True }}

end spec

end net
end Perennial
