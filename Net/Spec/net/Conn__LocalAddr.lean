/-
D18. `c.LocalAddr()` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`connAt`, with the
end's addresses `la`, `ra`), through the interface (`conn.LocalAddr.impl`, promoted): `la`, the
same non-nil `*TCPAddr` at every call, whatever the connection's state (`connAt`'s `netAddr la`).
Proved in `Net/Proof/net/Conn__LocalAddr.lean`.
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
abbrev Conn.LocalAddr.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface),
  {{ connAt (GF := GF) t cn s a la ra }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"LocalAddr" #t)) (Val #()))
  {{ RET #la; True }}

end spec

end net
end Perennial
