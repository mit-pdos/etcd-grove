/- Lean-first (no Rocq counterpart).

`Server()`: the driver's server machine (see `rpcdriver.go`): it never panics. In the run's world
(`drvWorld γid reg`): the registered codec; `DefaultServer`'s registry, owned and empty
(`defaultServerO γs γf ∗ svcOwn γf ∅`, net/rpc's first initialization); the right to register on
`DefaultServeMux` (`muxOwn (globalAddr net.http.defaultServeMux) []`, net/http's); its listeners' protocols (`rpcLisP`, raw at
`TCPAddr`, behind the `CONNECT` handshake at `HTTPAddr`); the machine's thread bound (net/rpc's
server); and the package facts its callees read.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Codec
public import Net.Proof.net.http.MuxDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Base
public import Perennial.Proof.log.Base

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
abbrev Server.spec : Prop :=
  ∀ (γid reg γs γf : GName),
  {{ drvFacts ∗ net.rpc.codecSet drvCodec ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ isPkgInit (PROP := IProp GF) pkg_id.log ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service ∗
      net.rpc.srvEnv ∗ globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus ∗ net.http.httpSrvEnv (GF := GF) ∗
      net.rpc.defaultServerO γs γf ∗ net.rpc.svcOwn γf ∅ ∗ net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) [] ∗
      net.rpc.rpcLisP (Gg := hG.goose_globalGS) (drvWorld γid reg) tcpAddr [] [] ∗
      net.rpc.rpcLisP (Gg := hG.goose_globalGS) (drvWorld γid reg) httpAddr
        (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns }}
    (App (Val (@! Server)) (Val #()))
  {{ RET #(); True }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
