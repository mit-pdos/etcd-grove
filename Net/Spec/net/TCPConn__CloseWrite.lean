/-
`t.CloseWrite()` on a `*TCPConn` `t` that is the end `s` of a TCP connection `cn` (`connAt`; a
`Conn` with `isConn` holds such a `t`, so `c.(*net.TCPConn)` succeeds; the model
`TCPConn.CloseWrite.impl`, `Net/TrustedCode/net.lean`): the extension's `CloseWrite`, whose
outcome the caller takes by a logically atomic update over the end's state and the direction from
it (`CloseWriteOutcome`, `GooseLang/Ext/Net/Impl.lean`, D4: the direction shut if open, or a `sys`
error that changes nothing; `closed` on a closed end). Its result `Q res` is handed back with the
error: `nil` for success, else the `*OpError{Op: "close", Source: la, Addr: ra}` of the failure's
kind (`resErr`; a `sys` error's call `"shutdown"`, no timeout). Proved in
`Net/Proof/net/TCPConn__CloseWrite.lean`.
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
abbrev TCPConn.CloseWrite.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface)
    (Q : Option NetErr → IProp GF),
  {{ connAt (GF := GF) t cn s a la ra ∗
      (|={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗ netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
        ∀ res d', ⌜CloseWriteOutcome st d res d'⌝ -∗ netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ Q res) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"CloseWrite" #t)) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ res, Q res ∗ resErr res go!"close" la ra none (· = go!"shutdown") err }}

end spec

end net
end Perennial
