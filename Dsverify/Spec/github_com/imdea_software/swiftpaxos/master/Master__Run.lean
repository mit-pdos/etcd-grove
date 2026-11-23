/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/master/Master__Run.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`m.Run()`: registers the master's rpc service, listens on `":port"` (the master's address on
node 1), serves it (`http.Serve`, which never returns), and in another goroutine waits for the
replicas, dials their rpc ports, makes the first leader and pings them, making another one
`BeTheLeader` when the leader's ping fails.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec

-- PORT: lab imports dropped: Harness.Proof.net.rpc.Results

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

/-- Never returns (change log C7: the whole service map at `masterAddr`): from the created
master on the master's port (`masterAddr`, its token and
the node's IP for the wildcard listen), the rpc world's addresses (the master's, with its
service, and the replicas', which it calls), the codec, and the node's `http` mux (unclaimed:
`HandleHTTP` claims the rpc path). -/
abbrev master.Master.Run.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.created m γc γm N (W64 7001) ∗ addrTok masterAddr ∗ nodeIp go!"10.77.0.17" ∗
      net.http.muxOwner [] ∗
      ([∗list] a ∈ rpcAddrs, net.rpc.rpcAddr W a) ∗
      ⌜(∀ svc, W.SS masterAddr svc =
          if svc = go!"Master" then some (sp.masterSpec γc γm) else none) ∧
        ∀ a ∈ replicaRpcAddrs, W.SS a go!"Replica" = some (sp.replicaRpcSpec γc γm)⌝ ∗
      net.rpc.codecSet ∗ net.rpc.kitCodecOk ∗ net.rpc.kitNameOk }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Run")) (Val #()))
  {{ RET #(); False }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
