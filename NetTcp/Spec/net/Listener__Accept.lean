/-
`li.Accept()` on a `Listener` `li` that is this node's listener `l` at `a` (`isListener`: a
`*TCPListener` `t` holding `l`; `tcpLisAt`), through the interface (stated on the resolved method,
the form a call on `li` takes once `li` is destructed) (`TCPListener.Accept.impl`,
`NetTcp/TrustedCode/net.lean`): the extension's `Accept`, by a logically atomic update over the
listener's state (`tcpLis l a o`, which may be in an invariant: a listener shared between threads)
and `a`'s pending set (`tcpPend`). A failure leaves both as they were and gives the caller's
`Qfail`; only if the listener is open (`o = true`), a connection `cn` pending at `a` is taken out
of the pending set, and the call returns its acceptor's end as a `Conn` (`isConn _ cn true a`)
with `Qok cn`. So an `Accept` of a closed listener fails. Proved in
`NetTcp/Proof/net/Listener__Accept.lean`.
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
abbrev Listener.Accept.spec : Prop :=
  ∀ (t : Loc) (l : w64) (a : GoString) (Qfail : IProp GF) (Qok : Nat → IProp GF),
  {{ t ↦□ (TCPListener.mk l) ∗ tcpLisAt (extLocalGS tcpExt (L := hG.goose_localGS)) l a ∗
      (|={⊤,∅}=> ∃ o S, tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l a o ∗
        tcpPend (extGlobalGS tcpExt (G := hG.goose_globalGS)) a S ∗
        ((tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l a o -∗
            tcpPend (extGlobalGS tcpExt (G := hG.goose_globalGS)) a S ={∅,⊤}=∗ Qfail) ∧
          (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l a o -∗
            tcpPend (extGlobalGS tcpExt (G := hG.goose_globalGS)) a (S \ {[cn]}) -∗
            tcpConnAt (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn a ={∅,⊤}=∗ Qok cn))) }}
    (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"Accept" #t)) (Val #()))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn, isConn c cn true a ∗ Qok cn) ∨ (⌜netErr err⌝ ∗ Qfail) }}

end spec

end net
end Perennial
