/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/master/Master__Run.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`m.Run()`: registers the master's rpc service on `DefaultServer` (`rpc.Register`), routes it over
HTTP (`rpc.HandleHTTP`), listens on the wildcard `":7001"` and serves it (`http.Serve`, which
returns only on a listener error), and in another goroutine waits for the replicas, dials their rpc ports, makes the
first leader and pings them, making another one `BeTheLeader` when the leader's ping fails.

Changed against the lab (notes/dsv-swiftpaxos.md, "The HTTP path"): the lab's `addrTok`/`nodeIp`
of its wildcard listen, `net.http.muxOwner`, `rpcAddr`s and `kitNameOk` are gone. The master's
port is the listener address's rpc protocols (`RpcHttpHyp.rpcLisP W ":7001"`, which gives the
right to listen there), the master's service is `withErr masterSpec` at every address the wildcard
takes (net/rpc's server may answer an error), and the replicas' rpc ports are dialed over HTTP
(`rpcHttp`). net/rpc's and net/http's packages, the server's bounds and package variables
(`threadBound`, `srvEnv`) and the registered codec are the server's.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [H : RpcHttpHyp netDistGF]

/-- The master's world: every address the wildcard `":7001"` takes offers the master's service
only, and every replica's rpc port the replica's. -/
def master.worldOk (γc γm : GName) (W : net.rpc.RpcWorld netDistGF) : Prop :=
  (∀ a svc, lisAccepts go!":7001" a →
      W.SS a svc = if svc = go!"Master" then some (withErr (sp.masterSpec γc γm)) else none) ∧
    ∀ a ∈ replicaRpcAddrs, W.SS a go!"Replica" = some (withErr (sp.replicaRpcSpec γc γm))

/-- Returns only if `http.Serve` does (on a listener error): see the file header. -/
abbrev master.Master.Run.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.created m γc γm N (W64 7001) ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net.http ∗
      ⌜threadBound netDistGF ≤ 2 ^ 31⌝ ∗ net.rpc.srvEnv ∗
      H.rpcLisP W go!":7001" (connectReq defaultRPCPath) connectAns ∗
      ([∗list] a ∈ replicaRpcAddrs, rpcHttp W a) ∗ ⌜master.worldOk γc γm W⌝ ∗
      net.rpc.codecSet net.rpc.RpcCodec.spec }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
