/-
`net.Listen("tcp", a)` for a string `a` that resolves to the plan address `a0` at this node's host
(`ListenAt` over the network's plan, `GooseLang/Ext/Tcp/Impl.lean`, D6, D21: `a` itself, or a
wildcard `":p"`, `"0.0.0.0:p"`, `"[::]:p"` for the plan's only address with port `p`; for a plan
address, `listenAt_self`), through `Listen.impl` (`NetTcp/TrustedCode/net.lean`): the extension's
`Listen`. A new open listener `l` at `a0`, as a `Listener` (`isListener`, the node's
`tcpLis l a0 true`, and `tcpLisAt l a0`, persistent, which `Accept` and `Close` need), or the
`*OpError{Op: "listen", Source: nil, Addr: x}`, `x` a `*TCPAddr`, whose `Err` is an
`*os.SyscallError` (`resErr`, D14). Proved in `NetTcp/Proof/net/Listen.lean`.
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
  ∀ (a a0 : GoString),
  {{ ⌜ListenAt (extGlobalGS tcpExt (G := hG.goose_globalGS)).plan (extLocalGS tcpExt (L := hG.goose_localGS)).host a a0⌝ }}
    (App (App (Val (@! net.Listen)) (Val #(go!"tcp"))) (Val #a))
  {{ (li : GoInterface) (err : GoInterface), RET (PairV #li #err);
      (⌜err = interface.nil⌝ ∗ ∃ l, isListener li l ∗ tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l a0 true ∗
        tcpLisAt (extLocalGS tcpExt (L := hG.goose_localGS)) l a0) ∨
      (∃ x, tcpAddr x ∗ resErr (some .sys) go!"listen" interface.nil x none (fun _ => True) err) }}

end spec

end net
end Perennial
