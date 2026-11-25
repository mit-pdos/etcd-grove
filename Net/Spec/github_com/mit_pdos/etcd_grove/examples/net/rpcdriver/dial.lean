/- Lean-first (no Rocq counterpart).

`dial()`: a client connected to the server over raw TCP (`TCPAddr`) or over HTTP (`HTTPAddr`), at
random; or an error (nothing is asserted of a failed dial).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Defs
public import Net.Spec.net.rpc.DialHTTP
public import Net.Spec.net.rpc.Dial

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev dial.spec : Prop :=
  ∀ (W : net.rpc.RpcWorld GF),
  {{ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ net.rpc.cliEnv ∗ net.http.httpEnv ∗
      globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus ∗
      net.rpc.rpcAddr (Gg := hG.goose_globalGS) W tcpAddr ∗
      net.rpc.rpcAddrP (Gg := hG.goose_globalGS) W httpAddr
        (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns }}
    (App (Val (@! dial)) (Val #()))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ a : GoString, ⌜a = tcpAddr ∨ a = httpAddr⌝ ∗ net.rpc.isClient c W a) ∨
      ⌜err ≠ interface.nil⌝ }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
