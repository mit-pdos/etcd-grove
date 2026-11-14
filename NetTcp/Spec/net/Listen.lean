/-
`net.Listen("tcp", a)` for an address `a` of the plan at this node's host (`tcpPlan`; `Listen.impl`,
`NetTcp/TrustedCode/net.lean`): the extension's `Listen`. A new open listener `l` at `a`, as a
`Listener` (`isListener`, the node's `tcpLis l a true`, and `tcpLisAt l a`, persistent, which
`Accept` and `Close` need), or an `*OpError`. Proved in
`NetTcp/Proof/net/Listen.lean`.
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
abbrev Listen.spec : Prop :=
  ∀ (a : GoString),
  {{ tcpPlan (extGlobalGS tcpExt (G := hG.goose_globalGS)) a
      (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
    (App (App (Val (@! net.Listen)) (Val #(go!"tcp"))) (Val #a))
  {{ (li : GoInterface) (err : GoInterface), RET (PairV #li #err);
      (⌜err = interface.nil⌝ ∗ ∃ l, isListener li l ∗
        tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l a true ∗
        tcpLisAt (extLocalGS tcpExt (L := hG.goose_localGS)) l a) ∨ ⌜netErr err⌝ }}

end spec

end net
end Perennial
