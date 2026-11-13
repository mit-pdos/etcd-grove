/-
`li.Accept()` on a `Listener` `li` that is this node's listener `l` at `a` (`isListener`: a
`*TCPListener` `t` holding `l`; `tcpLis`), through the interface (stated on the resolved method, the
form a call on `li` takes once `li` is destructed) (`TCPListener.Accept.impl`, `NetTcp/TrustedCode/net.lean`): the
extension's `Accept`. A failure gives the caller's `Qfail`; a connection `cn` pending at `a` is
taken by a logically atomic update over `a`'s pending set (`tcpPend`), and the call returns its
acceptor's end as a `Conn` (`isConn _ cn true a`) with `Qok cn`. Proved in
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
  ∀ (t : Loc) (l : w64) (a : GoString) (o : Bool) (Qfail : IProp GF)
    (Qok : Nat → IProp GF),
  {{ t ↦□ (TCPListener.mk l) ∗ tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l a o ∗
      ((tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l a o -∗ Qfail) ∧
        |={⊤,∅}=> ∃ S, tcpPend (extGlobalGS tcpExt (G := hG.goose_globalGS)) a S ∗
          ∀ cn, ⌜cn ∈ S⌝ -∗ tcpPend (extGlobalGS tcpExt (G := hG.goose_globalGS)) a (S \ {[cn]})
            ={∅,⊤}=∗ (tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l a o -∗
              tcpConnAt (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn a -∗ Qok cn)) }}
    (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"Accept" #t)) (Val #()))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn, isConn c cn true a ∗ Qok cn) ∨ (⌜netErr err⌝ ∗ Qfail) }}

end spec

end net
end Perennial
