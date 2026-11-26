/-
D18. `c.RemoteAddr()` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`connAt`, with
the end's addresses `la`, `ra`), through the interface (`conn.RemoteAddr.impl`, promoted): `ra`, the
same non-nil `*TCPAddr` at every call, whatever the connection's state (`connAt`'s `netAddr ra`).
Proved in `Net/Proof/net/Conn__RemoteAddr.lean`.
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
abbrev Conn.RemoteAddr.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface),
  {{ connAt (GF := GF) t cn s a la ra }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"RemoteAddr" #t)) (Val #()))
  {{ RET #ra; True }}

end spec

end net
end Perennial
