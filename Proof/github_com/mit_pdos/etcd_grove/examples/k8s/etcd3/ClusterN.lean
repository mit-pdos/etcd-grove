/-
**The k8s etcd3 driver's `k`-member cluster: its named premises and vocabulary** (stage A of
`notes/k8s-7f6-scope.md`, 2026-11-16; the user's decision (b): the cluster and partition theorems
for `k` members, `1 ≤ k ≤ 1000`, on the generic start, as putgetN/txnlinfaultsN). Lean-first (no
Rocq counterpart). txnlinfaultsN's (`etcd/txnlinfaultsN/Defs.lean`) at `startCluster`'s members
(`examples/k8s/etcd3/k8setcd3.go`), with one kubernetes client of the `k` bridges in place of `k`
etcd clients.

**The members** (`members k`, `etcdstart.Members("k8setcd3N", k, 20000, 21000)`): member `i`
(from `0`) named `k8setcd3N-i`, peer address `127.0.0.1:(20000+i)`, client address
`127.0.0.1:(21000+i)`, every client address served (`startOf`), to the member's bridge at
`127.0.0.1:(22000+i)` (`bridgeAt`, `bridges k`).

**The pure facts** (`BootFacts`, putgetN's): the member ids `ids` in the members' order (etcd's,
from each peer URL and the cluster token `k8setcd3N-6285`; `TestMemberIDs` checks their 16 low
bits distinct and not `0` for every `k ≤ 1000`), the peers `ps` in `bootstrap`'s order, a
permutation of the ids, and the bootstrap log.

**The Iris premises** (`premises`, persistent): putgetN's at these members and token.

**The cluster started, with its client** (`clusterUp`, `startCluster`'s success): the members'
slice and the bridges'; each member, at its bridge's address, with etcd's KV calls registered and
the address refusal-free, its KV names agreeing with the cluster's; each member's place in the
network (what the partitioner takes); each bridge owned and not blackholed; the kubernetes client
`kubernetes.New`'s over the `k` bridges; the client's view of etcd's KV at the start store; and (stage
E of 7f-6, checkpoint E-1) each member's watch registration at its bridge's address
(`etcdstart.watchRegAt`, its server `w.1` and watch server `w.2`) with its read view, the members'
names those of one history (`memberOf`, at the first member's read names `γrc`), and the client's
watch environment the members' (`watchEnvL`, `wmemsOf`): what a watcher of the client needs, but the
watch condition (`srvOnce`), which the instance's invariant gives later.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchServed
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchEnvL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3N

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

section pure
variable [GooseExts]

/-- **The members of the cluster** (`Members("k8setcd3N", k, PeerBase, ClientBase)`). -/
abbrev members (k : Nat) : List GMember := membersOf go!"k8setcd3N" k (W64 20000) (W64 21000)

/-- The cluster's token (`Token`). -/
abbrev token : GoString := go!"k8setcd3N-6285"

/-- **Member `i`'s bridge address** (`bridgeAddr(i)`): `127.0.0.1:(22000+i)`. -/
def bridgeAt (i : w64) : GoString := go!"127.0.0.1:" ++ decStr (W64 22000 + i)

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

/-- **The cluster's named premises** (persistent; see the file header), at the bound `N` of each
member's apply thread's write tokens, the member ids (in the members' order), the peers, their
contexts and the bootstrap log. putgetN's at these members and token. -/
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

section wmems
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The members as a watcher's environment lists them** (`etcdstart.watchEnvL`'s): each member's
address (its bridge's), watch server and the server's watch facts. -/
def wmemsOf (svs : List (EtcdGrove.client.SrvAt GF)) (ws : List (Loc × v3rpc.WSrv GF)) :
    List (etcdstart.WMem GF) :=
  List.zipWith (fun sv w => (sv.addr, w.2, etcdstart.srvWOf sv.E sv.γr false)) svs ws

/-- The prefix of the client's watch environment (any non-empty one: `wsReqOk` does not read it). -/
abbrev wpfx : GoString := go!"k"

end wmems

section cluster
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The cluster started, with its client** (`startCluster`'s success; see the file header), at
the bootstrap log `bootLog`: the members `ss`, the bridges `bs`, the kubernetes client `kc` over
the etcd client `cl`, the members as the client reaches them (`svs`, each at its bridge's address),
the cluster's KV names `γk` and its network `γn`. -/
def clusterUp (k : Nat) (bootLog : List EntryM) (srvs brs : GoSlice) (kc : Loc) : IProp GF :=
  iprop(∃ (γk : KVNames) (γn : NetNames GF) (ss : List Loc) (bs : List GoInterface) (cl : Loc)
      (V : EtcdGrove.client.WEnv GF) (svs : List (EtcdGrove.client.SrvAt GF))
      (ws : List (Loc × v3rpc.WSrv GF)) (γrc : ReadNames) (m0 : etcdstart.WMem GF),
    srvs ↦*□ ss ∗ brs ↦*□ bs ∗
    kc ↦□ (go_etcd_io.etcd.client.v3.kubernetes.Client.mk cl
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #kc)) ∗
    isNewClient cl (bridges k) V ∗
    ⌜ss.length = k ∧ svs.map EtcdGrove.client.SrvAt.addr = bridges k ∧ γk.log0 = [[], []] ∧
      ∀ sv ∈ svs, kvSame sv.γr.kv γk ∧ noRefusalAt sv.addr⌝ ∗
    ([∗list] sv ∈ svs, EtcdGrove.client.kvRegsAt sv) ∗
    ([∗list] s ∈ ss, ∃ id : w64, etcdstart.srvPeerCtl γn s id) ∗
    ([∗list] br ∈ bs, ∃ addr : GoString, bridge.ownBridge br addr false) ∗
    etcdKV γk (kvModelSt γk (bootEntries bootLog)) ∗
    ([∗list] sv; w ∈ svs; ws, etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗
      isServerRead w.1 sv.E sv.γr) ∗
    ⌜kvSame γrc.kv γk ∧ γrc.kv.log0 = [[], []] ∧
      (∀ sv ∈ svs, v3rpc.memberOf γrc.raft γrc.kv sv.γr) ∧
      V = etcdstart.watchEnvL m0 (wmemsOf svs ws) γrc wpfx⌝)

end cluster

end k8s_etcd3N
end EtcdGrove
end Perennial
