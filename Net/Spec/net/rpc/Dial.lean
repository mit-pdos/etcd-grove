/-
`Dial(nw, a)` (`nw` `"tcp"` or `"tcp4"`) to an rpc address `a` of world `W` (`rpcAddr`):
`net.Dial` (the library's `dial_au`), the connection registered in `W`, then `NewClient`: a client
of `a`, or the dial's error (with its `Error()`, `errAny`). Proved in `Net/Proof/net/rpc/Dial.lean`.
-/
module

public import Net.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Dial.spec : Prop :=
  ∀ (nw : GoString), net.tcpNet nw → ∀ (W : RpcWorld GF) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ rpcAddr (Gg := hG.goose_globalGS) W a }}
    (App (App (Val (@! net.rpc.Dial)) (Val #nw)) (Val #a))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}

end spec

end net.rpc
end Perennial
