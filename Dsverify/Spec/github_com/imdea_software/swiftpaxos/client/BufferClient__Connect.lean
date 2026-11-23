/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/BufferClient__Connect.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`b.Connect()` (`Client.Connect` through the embedding): the master's `GetReplicaList` and
`GetLeader` over `net/rpc`, then a connection to every replica the master lists as alive.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions] -- change log C4 (`failed`)
variable [client.Assumptions] [examples.swiftnet.Assumptions]

/-- From a fresh buffer client of the master's address, the master's rpc address and service,
the replicas' ports' protocols and the protocol's invariant: connected (the membership of the
configuration's `N` replicas; one registered connection of kind `client cid` per alive
replica) or an error (any step may fail: dials, the calls' 3 s timeouts, the network's faults). -/
abbrev client.BufferClient.Connect.spec : Prop :=
  ∀ (b : Loc) (cid : w32) (maddr : GoString) (mport : w64) (W : net.rpc.RpcWorld netDistGF)
    (γ : sp.Names) (γc γm γl : GName),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.bufFresh b cid maddr mport ∗ ⌜sp.addrPort maddr mport = masterAddr⌝ ∗
      net.rpc.rpcAddr W masterAddr ∗ ⌜W.SS masterAddr go!"Master" = some (sp.masterSpec γc γm)⌝ ∗
      net.rpc.codecSet ∗ net.rpc.kitCodecOk ∗
      ([∗list] a ∈ replicaAddrs, addrProto a (sp.inP γ γc γm) (sp.outQ γ γc γm)) ∗
      sp.inv γ γc γm γl }}
    (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Connect")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ N : Nat, client.connected b γ γc γm cid N) ∨
      (⌜err ≠ interface.nil⌝ ∗ client.failed b) }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
