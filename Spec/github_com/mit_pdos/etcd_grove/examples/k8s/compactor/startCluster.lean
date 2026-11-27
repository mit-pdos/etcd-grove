/-
`startCluster(k, lg)` (`examples/k8s/compactor/compactor.go`; `notes/k8s-compactor-n-plan.md`): the k8s
etcd3 driver's `startCluster` without its kubernetes client, returning the bridges' addresses instead.
The `k` members started (`etcdstart.Members`, `etcdstart.StartMembers` at cluster3's snapshot settings,
in compaction mode: every compaction a client's), then each member's gRPC server on its client address
(`etcdstart.Serve`, with a `holdToken` goroutine whose thread token the member's serving takes) and a
bridge to it (`cluster3.StartBridge`). Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the logger a zap logger, the members' start bundles
(each its WAL directory fresh, its peer and client addresses free, the peer's HTTP protocol
unregistered), the bridges' addresses free, the thread token and the cluster's named premises
(`k8s_compactorN.premises`), `startCluster(k, lg)` returns the members, the bridges, the bridges'
addresses and `ok`: `false` (a step failed, nothing else promised), or `true` with the thread token and
the cluster up (`k8s_compactorN.clusterUp`).

**The pure premises:** the etcd3 driver's `startCluster`'s (the member count, the ids, `BootFacts`,
the budgets, v3rpc's method sets), the bounds the adequacy theorem fixes as instance binders.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ClusterN

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver k8s_compactorN

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

/-- See the file header. -/
abbrev startCluster.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (lg : Loc)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  1 ≤ k → k ≤ 1000 → ids.length = k →
  BootFacts ids ps ctxs boot →
  srvLevels (GF := GF) →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor ∗
      zapLoggerOk lg ∗
      ([∗list] m ∈ k8s_etcd3N.startOf (members k), etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] b ∈ bridges k, netAddrFree (GF := GF) b) ∗
      threadTok ∗ premises k N ids ps ctxs boot }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.startCluster))
      (Val #(W64 k))) (Val #lg))
  {{ (srvs brs baddrs : GoSlice) (ok : Bool), RET (PairV (PairV (PairV #srvs #brs) #baddrs) #ok);
      ⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ threadTok ∗ clusterUp k (LogEntry.toEntries boot 0) srvs brs baddrs) }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
