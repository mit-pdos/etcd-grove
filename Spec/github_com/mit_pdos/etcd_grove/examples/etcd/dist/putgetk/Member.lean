/-
`Member(i, peers, clients)` (`examples/etcd/dist/putgetk/putgetk.go`): member `i` of a new cluster, on a
machine of its own (`notes/putget-dist-plan.md` §13, plan item 4). Lean-first (no Rocq counterpart).

The program: the initial cluster's map (member `j` named `Name(j)`, its one peer URL `http://peers[j]`),
`etcdstart.StartMember` of member `i` (its raft handler served on its peer address, the server started),
`etcdstart.Serve` at `clients[i]`, then `holdForever()`; it returns only when a step fails.

**The triple**, for any list of members `ms` (Go's `etcdstart.Member` values: name, peer address, client
address) with the ids `ids` (in the members' order) and any `i < ms.length`: from the slices `peers` and
`clients` of the members' addresses, member `i`'s named premises (the in-process `putgetN`'s, audited:
`bootPremise` at `putgetN`'s directory `dirN ms ids` and `urlsN ms m`, `bootMarshal`, `commonPremises`), its
machine's start (`ETCD_VERIFY` off, its WAL area and data directory fresh), its share of the cluster's start
(`etcd_dist.memberStartShare` of `etcdClusterStart`, at S5's names `S5` and the cluster's names `c`, lease
mode `none`), and the publication obligation (`memberPubOkK`), `Member` returns (only on an error: else it
holds forever). The member's peer half (`StartMember` on a member machine) is S5's: its proof takes
`etcd_dist.StartMember_dist.spec S5` as a named hypothesis.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
abbrev Member.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : Net.NetProtoGS]
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 28)]
    (S5 : etcd_dist.S5Draft (G := hG.goose_globalGS) GF)
    (ms : List GMember) (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (i : Nat) (m : GMember) (id : w64) (cm : etcd_dist.ClusterMember) (c : etcd_dist.ClusterNames)
    (γE : GName) (Pub : etcd_dist.EnvView → IProp GF) (peersSl clientsSl : GoSlice),
  -- the cluster: `bootstrap`'s results (`putgetN`'s), member `i` among the members
  etcd_putgetN.BootFacts ids ps ctxs boot → ms.length = ids.length → ms.length < 2 ^ 63 →
  ms[i]? = some m → ids[i]? = some id → (cmsOf ms ids)[i]? = some cm →
  -- the members' names as `Name` computes them, their peer addresses distinct, each name valid UTF-8 and
  -- at most 200 bytes (`StartMember`'s), each peer URL plain (`host:port`)
  (∀ (j : Nat) (n : GMember), ms[j]? = some n → n.Name' = nameOf j) →
  (ms.map (·.Peer')).Nodup →
  (∀ n ∈ ms, utf8Valid n.Name' ∧ n.Name'.length ≤ 200 ∧
    types.plainPeerURL (go!"http://" ++ n.Peer')) →
  -- the cluster's names, as `etcdClusterStart` chose them (lease mode `none`, no compaction)
  etcd_dist.ClusterOk c ps boot .none false 0 ids →
  srvLevels (GF := GF) →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk ∗
      threadTok ∗
      peersSl ↦* ms.map (·.Peer') ∗ clientsSl ↦* ms.map (·.Client') ∗
      -- member `i`'s named premises (`putgetN`'s `premises`, at member `i`)
      bootPremise (2 ^ 28) ps (LogEntry.toEntries boot 0) ctxs (etcd_putgetN.dirN ms ids) go!"putgetk"
        m.Name' (urlsN ms m) id ∗
      bootMarshal ps ctxs (LogEntry.toEntries boot 0) ∗ commonPremises ∗
      -- the machine's start
      envVerifyOff (GF := GF) ∗ memberAreasFresh (GF := GF) (memberDataDir m.Name') ∗
      -- its share of the cluster's start, and what it publishes
      etcd_dist.memberStartShare (G := hG.goose_globalGS) S5 c (cmsOf ms ids) ps ctxs
        (LogEntry.toEntries boot 0) cm γE Pub ∗
      memberPubOkK c.γk Pub }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Member))
      (Val #(W64 i))) (Val #peersSl)) (Val #clientsSl))
  {{ RET #(); True }}

end spec

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
