/-
**txnlinfaultsN's `Main(k, clients, ops, sched)`: its named premises and vocabulary**
(`notes/txnlinfaultsN-plan.md`, 2026-11-15). Lean-first (no Rocq counterpart). partition's
(`partition/Defs.lean`) for the `k` members of `examples/etcd/txnlinfaultsN/txnlinfaultsN.go`, over
putgetN's generic start (`putgetN/Defs.lean`).

**The members** (`members k`, `etcdstart.Members("txnlinfaultsN", k, 26000, 27000)`): member `i`
(from `0`) named `txnlinfaultsN-i`, peer address `127.0.0.1:(26000+i)`, client address
`127.0.0.1:(27000+i)`, every client address served (`startOf`), to the member's bridge at
`127.0.0.1:(28000+i)` (`bridgeAt`, `bridges k`).

**The pure facts** (`BootFacts`, putgetN's): the member ids `ids` in the members' order (etcd's,
from each peer URL and the cluster token `txnlinfaultsN-12748`; `TestMemberIDs` checks their 16 low
bits distinct and not `0` for every `k ≤ 1000`), the peers `ps` in `bootstrap`'s order, a
permutation of the ids, and the bootstrap log.

**The Iris premises** (`premises`, persistent): putgetN's at this program's members and token:
`bootstrap`'s contract for every member at the URL directory `etcd_putgetN.dirN` (each member's one
peer URL), `proto.Marshal`'s contract at the bootstrap log's conf changes, the raft wrapper's
trust-boundary contracts.

**The cluster started, with its clients** (`clusterUp`, `startCluster`'s success): the members'
slice, the bridges' and the clients'; each member, at its bridge's address, with etcd's KV calls
registered and the address refusal-free, its KV names agreeing with the cluster's; each member's
place in the network (what the partitioner takes); each bridge owned and not blackholed; each client
`clientv3.New`'s over the `k` bridges; the client's view of etcd's KV at the start store.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlinfaultsN

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

section pure
variable [GooseExts]

/-- **The members of `Main(k)`'s cluster** (`Members("txnlinfaultsN", k, PeerBase, ClientBase)`). -/
abbrev members (k : Nat) : List GMember := membersOf go!"txnlinfaultsN" k (W64 26000) (W64 27000)

/-- The cluster's token (`Token`). -/
abbrev token : GoString := go!"txnlinfaultsN-12748"

/-- **Member `i`'s bridge address** (`bridgeAddr(i)`): `127.0.0.1:(28000+i)`. -/
def bridgeAt (i : w64) : GoString := go!"127.0.0.1:" ++ decStr (W64 28000 + i)

/-- **The bridges' addresses**, in the members' order. -/
def bridges (k : Nat) : List GoString := (List.range k).map (fun i : Nat => bridgeAt (W64 (i : Int)))

/-- **The program's start bundles** (name, peer address, client address): every member's, with its
client address (every member is served). -/
def startOf (ms : List GMember) : List (GoString × GoString × Option GoString) :=
  ms.map (fun m => (m.Name', m.Peer', some m.Client'))

/-- **`bootstrap`'s results, as Go computes them** (putgetN's: the ids in the members' order, the
peers a permutation of them, `BootCore`). -/
abbrev BootFacts (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry) :
    Prop :=
  etcd_putgetN.BootFacts ids ps ctxs bl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`Main(k, …)`'s named premises** (persistent; see the file header), at the bound `N` of each
member's apply thread's write tokens, the member ids (in the members' order), the peers, their
contexts and the bootstrap log. putgetN's at this program's members and token. -/
def premises (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  iprop(
    ([∗list] m; id ∈ members k; ids,
      etcdstart.bootPremise N ps (LogEntry.toEntries boot 0) ctxs (etcd_putgetN.dirN (members k) ids)
        token m.Name' (urlsN (members k) m) id))

instance premises_persistent (k N : Nat) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) k N ids ps ctxs boot) := by
  unfold premises; infer_instance

end defs

section cluster
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The cluster started, with its clients** (`startCluster`'s success; see the file header), at
the bootstrap log `bootLog`: the members `ss`, the bridges `bs`, the clients `cls` (`k` of them),
the members as the clients reach them (`svs`, each at its bridge's address), the cluster's KV names
`γk` and its network `γn`. -/
def clusterUp (k : Nat) (bootLog : List EntryM) (srvs brs clis : GoSlice) : IProp GF :=
  iprop(∃ (γk : KVNames) (γn : NetNames GF) (ss : List Loc) (bs : List GoInterface)
      (cls : List Loc) (svs : List (EtcdGrove.client.SrvAt GF)),
    srvs ↦*□ ss ∗ brs ↦*□ bs ∗ clis ↦* cls ∗
    ⌜cls.length = k ∧ svs.map EtcdGrove.client.SrvAt.addr = bridges k ∧ γk.log0 = [[], []] ∧
      ∀ sv ∈ svs, sv.γr.kv.st = γk.st ∧ noRefusalAt sv.addr⌝ ∗
    ([∗list] sv ∈ svs, EtcdGrove.client.kvRegsAt sv) ∗
    ([∗list] s ∈ ss, ∃ id : w64, etcdstart.srvPeerCtl γn s id) ∗
    ([∗list] br ∈ bs, ∃ addr : GoString, bridge.ownBridge br addr false) ∗
    ([∗list] cl ∈ cls, ∃ V : EtcdGrove.client.WEnv GF, isNewClient cl (bridges k) V) ∗
    etcdKV γk (kvModelSt γk (bootEntries bootLog)))

end cluster

end etcd_txnlinfaultsN
end EtcdGrove
end Perennial
