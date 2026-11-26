/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/New.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift.New(alias, rid, addrs, true, fr, true, false, pl, f, conf, lg, nil)`: the replica
constructor, as the adapter's `serve` calls it on replica node `k + 2` (its id `rid` and the
membership `addrs` from the master's `Register`): it builds the replica and starts its run
loop (connections to the peers, then the clients' acceptor), its batcher, sender and reply
channel. The hub of the replica side (HUBS.md: the constructor).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.config.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Dsverify.Spec.encoding.gob.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [examples.swiftnet.Assumptions] [net.rpc.Assumptions]

/-- `rpc.Register`'s obligation on the codec's `Receiver` for the replica `r` (not nil), once the
codec is registered and the replica's persistent facts (`rcvrRes`) hold: it returns a
`*Receiver` serving `withErr replicaRpcSpec` under the name `"Replica"` (`Net/`'s `rcvrIs`). -/
abbrev swift.rcvr.spec : Prop :=
  ∀ (r : Loc) (γc γm : GName),
  ⌜r ≠ null⌝ ∗ net.rpc.codecSet net.rpc.RpcCodec.spec ∗
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
    swift.rcvrRes r γc γm ⊢
    net.rpc.RpcCodec.spec.rcv (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #r)
      (net.rpc.rcvrIs net.rpc.RpcCodec.spec
        (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #r)
        (withErr (sp.replicaRpcSpec γc γm)) go!"Replica" false)

/-- From the replica node's protocol share, the protocol's invariant, the configuration (`N`
replicas, fast reads `fr`) and the membership `l` naming the node's port as replica `rid`'s,
the replicas' ports' protocols, the node's IP and its peer listener's protocols (it listens at
the wildcard `replica.wildOf a`, `":port"`), and the registered net/rpc codec: the replica,
running, and the codec's `Receiver` for it, serving the replicas' service
(`withErr replicaRpcSpec`) under the name `"Replica"` (`Net/`'s `rcvrIs`: what
`rpc.Register(rep)` asks; `swift.rcvr.spec`, a premise of `New`'s proof). The pool level `pl`
and `f` are the adapter's. Change log C14: `New` stores `cmap.SHARD_COUNT` and `useFastAckPool`, and its descriptors read
`MaxDescRoutines`: it takes the three globals' exclusive points-to, which the boot thread of a
replica node owns (a Go store is not atomic in Perennial). Change log C17: gob's codec is set
(`serve` calls `registerRPC` before `swift.New`): the run loop's message table decodes `MSync`s
with gob. Change log C21: `MaxDescRoutines` holds `0 ≤ d ≤ 100` (the adapter stores 0, 2 or 100;
the run loop allocates `d` reader bundles for its descriptors' count lock). -/
abbrev swift.New.spec : Prop :=
  ∀ (al : GoString) (rid : w64) (addrs : GoSlice) (l : List GoString) (N k : Nat) (fr : Bool)
    (pl f : w64) (cfgp lg : Loc) (γ : sp.Names) (γc γm γl : GName) (a ip : GoString),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ addrs ↦*□ l ∗
      ⌜replicaAddrs[k]? = some a ∧ l[uint.nat rid]? = some a ∧ ip ++ [W8 58] <+: a⌝ ∗
      sp.replicaStart γ k ∗ nodeIp ip ∗
      -- the peer listener's address (`waitForPeerConnections`' wildcard) and its protocols
      lisProto (replica.wildOf a) (sp.inP γ γc γm) (sp.outQ γ γc γm) ∗
      ([∗list] a' ∈ replicaAddrs, addrProto a' (sp.inP γ γc γm) (sp.outQ γ γc γm)) ∗
      config.plain cfgp fr ∗ dlog.quiet lg ∗
      ⌜uint.Z pl ≤ 2 ∧ uint.nat f = (N - 1) / 2⌝ ∗
      -- change log C14, change log C21 (`d`'s bound)
      (∃ (d : w64) (v : Bool) (n : w64), ⌜0 ≤ sint.Z d ∧ sint.Z d ≤ 100⌝ ∗
        globalAddr swift.MaxDescRoutines ↦ d ∗
        globalAddr swift.useFastAckPool ↦ v ∗
        typedPointsto (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT)
          n (DFrac.own 1)) ∗
      -- change log C17
      encoding.gob.codecSet (GF := netDistGF) ∗
      net.rpc.codecSet net.rpc.RpcCodec.spec ∗
      -- L2 (notes/prove-s2-e.md, item 4): the node's claimed ghost, for its protocol steps
      client.nodeGhostOk γ (sp.PNode.rep k) }}
    (App (App (App (App (App (App (App (App (App (App (App (App (Val (@! swift.New))
      (Val #al)) (Val #rid)) (Val #addrs)) (Val #true)) (Val #fr)) (Val #true)) (Val #false))
      (Val #pl)) (Val #f)) (Val #cfgp)) (Val #lg)) (Val #slice.nil))
  {{ (rep : Loc), RET #rep;
      net.rpc.RpcCodec.spec.rcv (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep)
        (net.rpc.rcvrIs net.rpc.RpcCodec.spec
          (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep)
          (withErr (sp.replicaRpcSpec γc γm)) go!"Replica" false) }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
