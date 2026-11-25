/-
`c.RemoteAddr().String()` on a connection of `Net/`'s model (the lab's
`net.TCPConn.RemoteAddr.wp_String`, `Harness/Proof/net/TCPConn__RemoteAddr.lean`): `RemoteAddr`
returns the connection end's `*TCPAddr` (`net.Conn.RemoteAddr.spec`, taken as a premise: the import
tiers), and `(*TCPAddr).String` is the model's arbitrary string (`Net/TrustedCode/net.lean`,
`TCPAddr.String.impl`, through `wp_net_AnyString`). Net has no spec of `TCPAddr.String`; this is
its proof over the model, not a hypothesis. (`c.RemoteAddr().String()` itself, at `serveClient`'s
call shape, is to be added with `N/Serve`.)
-/
module

public import Net.Spec.net.Conn__RemoteAddr
public import GooseLang.Ext.Net.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.lib

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics] [net.Assumptions]

/-- `(*TCPAddr).String()`: some string, for any receiver. -/
theorem wp_TCPAddr_String (x : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (x @!! go.GoType.PointerType net.TCPAddr.ty @!! go!"String")) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  wp_start
  (try wp_method_call)
  (try unfold net.TCPAddr.String.impl)
  (try wp_auto)
  iapply wp_net_AnyString
  iintro %s
  iapply HΦ; itrivial

end

end Perennial.gryff.lib
