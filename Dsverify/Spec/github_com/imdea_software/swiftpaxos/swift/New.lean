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
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.config.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Dsverify.Spec.encoding.gob.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [examples.swiftnet.Assumptions]

/-- From the replica node's protocol share, the protocol's invariant, the configuration (`N`
replicas, fast reads `fr`) and the membership `l` naming the node's port as replica `rid`'s,
the node's port's token, the replicas' ports' protocols, and the node's IP (its peer listener is
on `":port"`): the replica, running, whose rpc methods meet the replicas' service
(`rcvrOk`, for `rpc.Register`). The pool level `pl` and `f` are the adapter's. Change log C14:
`New` stores `cmap.SHARD_COUNT` and `useFastAckPool`, and its descriptors read
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
      sp.replicaStart γ k ∗ addrTok a ∗ nodeIp ip ∗
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
      -- L2 (notes/prove-s2-e.md, item 4): the node's claimed ghost, for its protocol steps
      client.nodeGhostOk γ (sp.PNode.rep k) }}
    (App (App (App (App (App (App (App (App (App (App (App (App (Val (@! swift.New))
      (Val #al)) (Val #rid)) (Val #addrs)) (Val #true)) (Val #fr)) (Val #true)) (Val #false))
      (Val #pl)) (Val #f)) (Val #cfgp)) (Val #lg)) (Val #slice.nil))
  {{ (rep : Loc), RET #rep;
      net.rpc.rcvrOk (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep)
        (sp.replicaRpcSpec γc γm) ∗
      net.rpc.RpcCodec.methods (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep) ∗
      ⌜net.rpc.RpcNames.name (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #rep) =
        go!"Replica"⌝ }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
