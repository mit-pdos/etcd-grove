/-
`c.Close()` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`isConn`), through the
interface (`conn.Close.impl`, promoted): the extension's `Close`, whose outcome the caller takes by
a logically atomic update over the end's state and its written bytes (`CloseRes`: the end closed,
and its FIN sent unless broken). Its result `Q ok` is handed back with the error: `nil` for `ok`,
else an `*OpError`. Proved in `NetTcp/Proof/net/Conn__Close.lean`.
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
  ∀ (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) (Q : Bool → IProp GF),
  {{ isConn (GF := GF) c cn s a ∗
      (|={⊤,∅}=> ∃ st r out f, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r ∗
        tcpOut (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st' r -∗
          tcpOut (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s out f' ={∅,⊤}=∗ Q ok) }}
    (App (App (Val (GoInstruction (MethodResolve Conn.ty go!"Close"))) (Val #c)) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ ok, Q ok ∗ ⌜(ok = true → err = interface.nil) ∧ (ok = false → netErr err)⌝ }}

end spec

end net
end Perennial
