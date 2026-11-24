/-
`li.Accept()` on a `Listener` `li` that is this node's listener `l` at `la` (`isListener`: a
`*TCPListener` `t` with `lisAt t l x`; `netLisOn`: `la` a valid address or a wildcard, D21), through
the interface (stated on the resolved method, the form a call on `li` takes once `li` is destructed)
(`TCPListener.Accept.impl`, `Net/TrustedCode/net.lean`): the extension's `Accept` (D7), by logically
atomic updates (opened only at the step that decides). A failure, by one over the listener's state
(`netLis l la o`, which may be in an invariant: a listener shared between threads), which it leaves
as it was, gives the caller's `Qfail k`, `k` `closed` if the listener is closed and `sys` if it is
open. Only if the listener is open, a connection `cn` dialed to a valid address `a` the listener
takes (`lisAccepts`: `la` itself if it is valid, any valid address with its port if it is a
wildcard) and pending there is taken out of `a`'s pending set (`netPend`), by an update over the
listener's state and that set which the caller gives for every such `a`, and the call returns its
acceptor's end as a `Conn` (`isConn _ cn true a`) with `Qok a cn`. A failure's error is the
`*OpError{Op: "accept", Source: nil, Addr: x}` of its kind (`resErr`; a `sys` error's call
`"accept4"`, or, `poll`, a bare `ENOMEM`/`ENOSPC`: `epollErr`, D7, Go's `netFD.accept` returning the
poller registration's error of the connection it took unwrapped, after closing it). Proved in `Net/Proof/net/Listener__Accept.lean`. Its instance at a valid address, with
one update over both cases, is `Listener.Accept.spec_addrOk` (`Net/Proof/net/AtAddr.lean`).
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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev Listener.Accept.spec : Prop :=
  ∀ (t : Loc) (l : w64) (x : GoInterface) (la : GoString) (Qfail : NetErr → IProp GF)
    (Qok : GoString → Nat → IProp GF),
  {{ lisAt (GF := GF) t l x ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
      ((|={⊤,∅}=> ∃ o, netLis (extLocalGS netExt (L := hG.goose_localGS)) l la o ∗
          (netLis (extLocalGS netExt (L := hG.goose_localGS)) l la o ={∅,⊤}=∗
            Qfail (if o then .sys else .closed))) ∧
        ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ -∗
          |={⊤,∅}=> ∃ o S, netLis (extLocalGS netExt (L := hG.goose_localGS)) l la o ∗
            netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a S ∗
            (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l la o -∗
              netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a (S \ {[cn]}) -∗
              netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a ={∅,⊤}=∗ Qok a cn)) }}
    (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"Accept" #t)) (Val #()))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn a, ⌜addrOk a = true ∧ lisAccepts la a⌝ ∗ isConn c cn true a ∗
        Qok a cn) ∨
      (∃ k, Qfail k ∗
        resErr (some k) go!"accept" interface.nil x none (· = go!"accept4") err (poll := true)) }}

end spec

end net
end Perennial
