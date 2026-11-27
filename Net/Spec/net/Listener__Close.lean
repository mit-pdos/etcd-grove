/-
`li.Close()` on a `Listener` `li` that is this node's listener `l` at `a` (`isListener`: a
`*TCPListener` `t` with `lisAt t l x`; `netLisOn`: `a` a valid address or a wildcard), through the interface (stated on the resolved
method) (`TCPListener.Close.impl`, `Net/TrustedCode/net.lean`): the extension's `LisClose` (D9,
D17), by a logically atomic update over the listener's state (`netLis l a o`, which may be in an
invariant: a listener shared with a thread blocked in `Accept`): the listener is closed, and the
result `Q res` (`LisCloseOutcome`: success if it was open, `closed` if not) is handed back with the
error: `nil` for success, else the `*OpError{Op: "close", Source: nil, Addr: x}` of its kind
(`resErr`). Proved in `Net/Proof/net/Listener__Close.lean`.
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
abbrev Listener.Close.spec : Prop :=
  ∀ (t : Loc) (l : w64) (x : GoInterface) (a : GoString) (Q : Option NetErr → IProp GF),
  {{ lisAt (GF := GF) t l x ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l a ∗
      (|={⊤,∅}=> ∃ o, netLis (extLocalGS netExt (L := hG.goose_localGS)) l a o ∗
        ∀ res, ⌜LisCloseOutcome o res false⌝ -∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a false ={∅,⊤}=∗ Q res) }}
    (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"Close" #t)) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ res, Q res ∗ resErr res go!"close" interface.nil x none (· = go!"close") err }}

end spec

end net
end Perennial
