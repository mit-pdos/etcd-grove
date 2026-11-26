/-
`DialHTTP(nw, a)`: `DialHTTPPath(nw, a, DefaultRPCPath)` (`defaultRPCPath`, `"/_goRPC_"`, where
`HandleHTTP` registers the server). Proved in `Net/Proof/net/rpc/DialHTTP.lean`.
-/
module

public import Net.Spec.net.rpc.DialHTTPPath

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev DialHTTP.spec : Prop :=
  ∀ (nw : GoString), net.tcpNet nw → ∀ (W : RpcWorld GF) (a : GoString),
  {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ net.http.httpEnv ∗
      globalAddr net.rpc.connected ↦□ connectedStatus ∗
      rpcAddrP (Gg := hG.goose_globalGS) W a (connectReq defaultRPCPath) connectAns }}
    (App (App (Val (@! net.rpc.DialHTTP)) (Val #nw)) (Val #a))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err) }}

/-- `DialHTTP.spec` whose error is `errPlain` (`DialHTTPPath.spec_plain`). Proved in
`Net/Proof/net/rpc/DialHTTP.lean`. -/
abbrev DialHTTP.spec_plain : Prop :=
  ∀ (nw : GoString), net.tcpNet nw → ∀ (W : RpcWorld GF) (a : GoString),
  {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ cliEnv ∗ net.http.httpEnv ∗
      globalAddr net.rpc.connected ↦□ connectedStatus ∗
      rpcAddrP (Gg := hG.goose_globalGS) W a (connectReq defaultRPCPath) connectAns }}
    (App (App (Val (@! net.rpc.DialHTTP)) (Val #nw)) (Val #a))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ isClient c W a) ∨
      (⌜err ≠ interface.nil⌝ ∗ models_lab.errPlain err) }}

end spec

end net.rpc
end Perennial
