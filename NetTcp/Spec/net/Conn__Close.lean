/-
`c.Close()` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`isConn`), through the
interface (`conn.Close.impl`, promoted): the extension's `Close`, whose outcome (`CloseOutcome`,
`GooseLang/Ext/Tcp/Impl.lean`, D3: the end closed, its direction shut if open; an error if closed
already) the caller takes by a logically atomic update over the end's state and the direction from
it (`tcpEnd`, `tcpDir`). Its result `Q ok` is handed back with the error: `nil` for `ok`, else an
`*OpError`. Proved in `NetTcp/Proof/net/Conn__Close.lean`.
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
abbrev Conn.Close.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (Q : Bool → IProp GF),
  {{ connAt (GF := GF) t cn s a ∗
      (|={⊤,∅}=> ∃ st d, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st ∗ tcpDir (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s d ∗
        ∀ ok st' d', ⌜CloseOutcome st d ok st' d'⌝ -∗ tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st' -∗
          tcpDir (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ Q ok) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Close" #t)) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ ok, Q ok ∗ ⌜(ok = true → err = interface.nil) ∧ (ok = false → netErr err)⌝ }}

end spec

end net
end Perennial
