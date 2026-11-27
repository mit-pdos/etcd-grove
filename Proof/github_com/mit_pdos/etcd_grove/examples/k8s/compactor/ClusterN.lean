/-
**The k8s compactor driver's `k`-member cluster: its named premises and vocabulary**
(`notes/k8s-compactor-n-plan.md`, 2026-11-20: `MainPartition` on `k` members, `1 ≤ k ≤ 600`, in place
of `cluster3.StartCluster`'s three). Lean-first (no Rocq counterpart). The k8s etcd3 driver's
(`k8s/etcd3/ClusterN.lean`) at `startCluster`'s members (`examples/k8s/compactor/compactor.go`), in
compaction mode (every compaction a client's), with the bridges' addresses' slice in place of a
kubernetes client.

**The members** (`members k`, `etcdstart.Members("k8scompactorN", k, 23000, 24000)`): member `i`
(from `0`) named `k8scompactorN-i`, peer address `127.0.0.1:(23000+i)`, client address
`127.0.0.1:(24000+i)`, every client address served (`k8s_etcd3N.startOf`), to the member's bridge at
`127.0.0.1:(25000+i)` (`bridgeAt`, `bridges k`).

**The pure facts** (`BootFacts`, putgetN's): the member ids `ids` in the members' order (etcd's, from
each peer URL and the cluster token `k8scompactorN-235946`; `examples/k8s/all`'s `TestMemberIDs` checks
their 16 low bits distinct and not `0` for every `k ≤ 600`, with the etcd3 driver's first 1000), the
peers `ps` in `bootstrap`'s order, a permutation of the ids, and the bootstrap log.

**The Iris premises** (`premises`, persistent): putgetN's at these members and token.

**The cluster started** (`clusterUp`, `startCluster`'s success): the members' slice, the bridges'
and the bridges' addresses'; each member, at its bridge's address, with etcd's KV calls registered and
the address refusal-free, its KV names agreeing with the cluster's; each member's place in the network
(what the partitioner takes); each bridge owned and not blackholed; the client's view of etcd's KV at
the start store, in compaction mode at retention `0`; and each member's watch registration at its
bridge's address with its read view, the members' names those of one history (`memberOf`, at the
read names `γrc`): what a client of the bridges and its watcher need.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClusterN

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactorN

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3 etcdstart

section pure
variable [GooseExts]

/-- **The members of the cluster** (`Members("k8scompactorN", k, PeerBase, ClientBase)`). -/
abbrev members (k : Nat) : List GMember := membersOf go!"k8scompactorN" k (W64 23000) (W64 24000)

/-- The cluster's token (`Token`). -/
abbrev token : GoString := go!"k8scompactorN-235946"

/-- **Member `i`'s bridge address** (`bridgeAddr(i)`): `127.0.0.1:(25000+i)`. -/
def bridgeAt (i : w64) : GoString := go!"127.0.0.1:" ++ decStr (W64 25000 + i)

/-- **The bridges' addresses**, in the members' order. -/
def bridges (k : Nat) : List GoString := (List.range k).map (fun i : Nat => bridgeAt (W64 (i : Int)))

/-- **`bootstrap`'s results, as Go computes them** (putgetN's). -/
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

section cluster
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The cluster started** (`startCluster`'s success; see the file header), at the bootstrap log
`bootLog`: the members `ss`, the bridges `bs`, the bridges' addresses, the members as a client of the
bridges reaches them (`svs`, each at its bridge's address) with their watch servers `ws`, the
cluster's KV names `γk` (in compaction mode at retention `0`), its network `γn` and the history's
read names `γrc`. -/
def clusterUp (k : Nat) (bootLog : List EntryM) (srvs brs baddrs : GoSlice) : IProp GF :=
  iprop(∃ (γk : KVNames) (γn : NetNames GF) (ss : List Loc) (bs : List GoInterface)
      (svs : List (EtcdGrove.client.SrvAt GF)) (ws : List (Loc × v3rpc.WSrv GF)) (γrc : ReadNames),
    srvs ↦*□ ss ∗ brs ↦* bs ∗ baddrs ↦* bridges k ∗
    ⌜ss.length = k ∧ svs.map EtcdGrove.client.SrvAt.addr = bridges k ∧ γk.log0 = [[], []] ∧
      γk.cmp = true ∧ γk.cret = 0 ∧
      ∀ sv ∈ svs, kvSame sv.γr.kv γk ∧ noRefusalAt sv.addr⌝ ∗
    ([∗list] sv ∈ svs, EtcdGrove.client.kvRegsAt sv) ∗
    ([∗list] s ∈ ss, ∃ id : w64, etcdstart.srvPeerCtl γn s id) ∗
    ([∗list] br ∈ bs, ∃ addr : GoString, bridge.ownBridge br addr false) ∗
    etcdKV γk (kvModelSt γk (bootEntries bootLog)) ∗
    ([∗list] sv; w ∈ svs; ws, etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗
      isServerRead w.1 sv.E sv.γr) ∗
    ⌜kvSame γrc.kv γk ∧ γrc.kv.log0 = [[], []] ∧
      (∀ sv ∈ svs, v3rpc.memberOf γrc.raft γrc.kv sv.γr)⌝)

end cluster

end k8s_compactorN
end EtcdGrove
end Perennial
