/-
`t.SetNoDelay(b)` on a `*TCPConn` `t` that is the end `s` of a TCP connection `cn` (`connAt`), D24
(`GooseLang/Ext/Net/Impl.lean`; the model `TCPConn.SetNoDelay.impl`,
`Net/TrustedCode/net.lean`): `TCP_NODELAY` (`tcpsockopt_posix.go`'s `setNoDelay`), the extension's `SetSockopt`, which changes no state. Its
outcome the caller takes by a logically atomic update over the end's state (`SockOptOutcome`:
`closed` on a closed end, else success), its result `Q res` handed back with the error:
`nil` for success, else the `*OpError{Op: "set"}` with `Source` `la`, `Addr` `ra` of the failure's kind
(`resErr`; a `sys` error's call `"setsockopt"`). Proved in `Net/Proof/net/TCPConn__SetNoDelay.lean`.
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
abbrev TCPConn.SetNoDelay.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (b : Bool)
    (Q : Option NetErr → IProp GF),
  {{ connAt (GF := GF) t cn s a la ra ∗
      (|={⊤,∅}=> ∃ st, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        ∀ res, ⌜SockOptOutcome st (some true) res⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ={∅,⊤}=∗ Q res) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"SetNoDelay" #t)) (Val #b))
  {{ (err : GoInterface), RET #err;
      ∃ res, Q res ∗ resErr res go!"set" la ra none (· = go!"setsockopt") err }}

end spec

end net
end Perennial
