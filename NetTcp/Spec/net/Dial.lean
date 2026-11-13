/-
`net.Dial("tcp", a)` for an address `a` of the plan (`tcpPlan`; `Dial.impl`,
`NetTcp/TrustedCode/net.lean`): the extension's `Dial`. A failure gives the caller's `Qfail`; a
new connection `cn` is taken by a logically atomic update over `a`'s pending set (`tcpPend`), which
gets `cn` (with both ends' fresh resources, `tcpFreshEnd`, and `tcpConnAt`), and the call returns
the dialer's end as a `Conn` (`isConn _ cn false a`) and `Qok cn`. Proved in
`NetTcp/Proof/net/Dial.lean`.
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
abbrev Dial.spec : Prop :=
  ∀ (a h : GoString) (Qfail : IProp GF) (Qok : Nat → IProp GF),
  {{ tcpPlan (extGlobalGS tcpExt (G := hG.goose_globalGS)) a h ∗
      (Qfail ∧
        |={⊤,∅}=> ∃ S, tcpPend (extGlobalGS tcpExt (G := hG.goose_globalGS)) a S ∗
          ∀ cn, ⌜cn ∉ S⌝ -∗ tcpPend (extGlobalGS tcpExt (G := hG.goose_globalGS)) a (S ∪ {[cn]}) -∗
            tcpConnAt (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn a -∗
            tcpFreshEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn false -∗
            tcpFreshEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn true ={∅,⊤}=∗ Qok cn) }}
    (App (App (Val (@! net.Dial)) (Val #(go!"tcp"))) (Val #a))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn, isConn c cn false a ∗ Qok cn) ∨ (⌜netErr err⌝ ∗ Qfail) }}

end spec

end net
end Perennial
