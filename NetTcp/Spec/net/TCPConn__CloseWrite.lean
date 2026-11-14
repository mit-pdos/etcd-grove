/-
`t.CloseWrite()` on a `*TCPConn` `t` that is the end `s` of a TCP connection `cn` (`connAt`; a
`Conn` with `isConn` holds such a `t`, so `c.(*net.TCPConn)` succeeds; the model
`TCPConn.CloseWrite.impl`, `NetTcp/TrustedCode/net.lean`): the extension's `CloseWrite`, whose
outcome the caller takes by a logically atomic update over the end's state and its written bytes
(`CloseWriteOutcome`, `GooseLang/Ext/Tcp/Impl.lean`, D4: the direction shut if open, or an error that changes nothing). Its result `Q ok` is handed back with the error: `nil` for
`ok`, else an `*OpError`. Proved in `NetTcp/Proof/net/TCPConn__CloseWrite.lean`.
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
abbrev TCPConn.CloseWrite.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (Q : Bool → IProp GF),
  {{ connAt (GF := GF) t cn s a ∗
      (|={⊤,∅}=> ∃ st d, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st ∗ tcpDir (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s d ∗
        ∀ ok d', ⌜CloseWriteOutcome st d ok d'⌝ -∗ tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st -∗
          tcpDir (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ Q ok) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"CloseWrite" #t)) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ ok, Q ok ∗ ⌜(ok = true → err = interface.nil) ∧ (ok = false → netErr err)⌝ }}

end spec

end net
end Perennial
