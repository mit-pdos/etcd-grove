/-
`MainPartition(k, sched)` (`examples/k8s/compactor/compactor.go`; K6 of `notes/k8s-compactor-plan.md`,
2026-11-05; on `k` members since `notes/k8s-compactor-n-plan.md`, 2026-11-20): `Main`'s workload on `k`
etcd members started in process (`startCluster`: each member's auto-compactor off, every compaction a
client's, Kubernetes' deployment), a bridge to each member's client address, a client of every bridge
that waits for the cluster to serve (`ready`), the partitioner forked on the schedule `sched`
(`cluster3.Partitioner`: the links between members cut and mended, the links between the clients
and a member blackholed, unblackholed or dropped, any steps), the writer, and five API servers,
each with its own client of every bridge, three with their own compactor, two sharing the process's
(`StartCompactorPerEndpoint`, registered at the `k` bridges), which `MainPartition` waits for.
Lean-first.

**The triple:** from the package's `isPkgInit`, the members' start bundles (each its WAL directory
fresh, its peer and client addresses free, the peer's HTTP protocol unregistered), the bridges'
addresses free, the schedule read-only (`sched ↦*□ steps`, for *every* list of steps), the main
thread's token, the cluster's premises (`k8s_compactorN.premises`, as the etcd3 driver's) and the
compactor registry's claims' authority with no endpoint claimed (`regAuth ∅`), `MainPartition`
returns: no check of an API server panics and no compactor round panics. The pure premises are the
etcd3 driver's `MainPartition.spec`'s on its cluster (the member count `1 ≤ k ≤ 1000`, the member ids
and bootstrap log, `BootFacts`, the thread and receipt bounds, the server's workload and effect
premises, gRPC's method sets, `errors.As`'s target).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ClusterN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Inv
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
abbrev MainPartition.spec : Prop :=
  ∀ (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (sched : GoSlice) (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step),
  1 ≤ k → k ≤ 1000 → ids.length = k →
  k8s_compactorN.BootFacts ids ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  -- (per-type stage B3) the levels of a thread token the members' gRPC runs use
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor ∗
      -- the members' start bundles (each its WAL directory fresh, its peer and client addresses
      -- free, the peer's HTTP protocol unregistered) and the bridges' addresses free
      ([∗list] m ∈ k8s_etcd3N.startOf (k8s_compactorN.members k),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] b ∈ k8s_compactorN.bridges k, netAddrFree (GF := GF) b) ∗
      sched ↦*□ steps ∗ threadTok ∗
      k8s_compactorN.premises k N ids ps ctxs boot ∗
      k8s.regAuth (∅ : GMap GoString GName) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition))
      (Val #(W64 k))) (Val #sched))
  {{ RET #(); True }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
