/- Lean-first (no Rocq counterpart).

`Client()`: the driver's client machine (see `rpcdriver.go`): it never panics. In the run's world
(`drvWorld γid reg`, `Svc.lean`): the server's two addresses with their protocols, the registered
codec, net/rpc's and net/http's client variables, and the authority of the request ids (none issued:
`γid`'s ghost map empty).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Codec

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
abbrev Client.spec : Prop :=
  ∀ (γid reg : GName),
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ threadTok ∗ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
      isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      drvFacts ∗ net.rpc.codecSet drvCodec ∗ ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ net.rpc.cliEnv ∗
      net.http.httpEnv ∗ globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus ∗
      net.rpc.rpcAddr (Gg := hG.goose_globalGS) (drvWorld γid reg) tcpAddr ∗
      net.rpc.rpcAddrP (Gg := hG.goose_globalGS) (drvWorld γid reg) httpAddr
        (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns ∗
      ghostMapAuth (K := w64) (V := Unit) γid 1 ∅ }}
    (App (Val (@! Client)) (Val #()))
  {{ RET #(); threadTok }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
