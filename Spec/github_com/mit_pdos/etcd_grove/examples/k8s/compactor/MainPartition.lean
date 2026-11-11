/-
`MainPartition(sched)` (`examples/k8s/compactor/compactor.go`; K6 of `notes/k8s-compactor-plan.md`,
2026-11-05): `Main`'s workload on three etcd members started in process (`cluster3.StartCluster` at the
example's configuration `clusterCfg`: each member's auto-compactor off, every compaction a client's,
Kubernetes' deployment), a bridge to each member's client address, a client of every bridge that
waits for the cluster to serve (`ready`), the partitioner forked on the schedule `sched`
(`cluster3.Partitioner`: the links between members cut and mended, the links between the clients
and a member blackholed, unblackholed or dropped, any steps), the writer, and five API servers,
each with its own client of every bridge, three with their own compactor, two sharing the process's
(`StartCompactorPerEndpoint`, registered at the three bridges), which `MainPartition` waits for.
Lean-first.

**The triple:** from the package's `isPkgInit`, the right to listen on the nine addresses (the
members' peer and client addresses, the bridges'), the members' peer addresses' HTTP rights, the
schedule read-only (`sched ↦*□ steps`, for *every* list of steps), the main thread's token, the
cluster's premises at the configuration (`cluster3.premises`, as `examples/etcd/partition`'s), fresh
WAL directories and the compactor registry's claims' authority with no endpoint claimed
(`regAuth ∅`), `MainPartition` returns: no check of an API server panics and no compactor round
panics. The pure premises are partition's `Main.spec`'s (the member ids and bootstrap log,
`BootFacts`, the thread and receipt bounds, the server's workload and effect premises, gRPC's method
sets, `errors.As`'s target).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Cluster
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
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (sched : GoSlice) (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step),
  cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  -- (per-type stage B3) the levels of a thread token the members' gRPC runs use
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor ∗
      -- (2026-11-05, hub step 7, D1) the cluster's start bundle: each member's (its WAL directory
      -- fresh, its peer and client addresses free, the peer's HTTP protocol unregistered) and the
      -- bridges' addresses free
      cluster3.startRes (GF := GF) clusterCfg ∗
      sched ↦*□ steps ∗ threadTok ∗
      cluster3.premises clusterCfg N id₁ id₂ id₃ ps ctxs boot ∗
      k8s.regAuth (∅ : GMap GoString GName) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition)) (Val #sched))
  {{ RET #(); True }}

end spec

end k8s_compactor
end EtcdGrove
end Perennial
