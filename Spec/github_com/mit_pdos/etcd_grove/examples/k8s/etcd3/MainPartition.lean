/- Lean-first (no Rocq counterpart).

`MainPartition(clients, ops, sched)` (`examples/k8s/etcd3/k8setcd3.go`; step 2 of "k8s etcd3 over
cluster3" in `notes/k8s-etcd3-plan.md`, 2026-11-07): `MainCluster` under the partition schedule
`sched`. Once the store is made, `cluster3.Partitioner` runs the schedule on a goroutine of its
own (peer cuts and mends, a member's bridge blackholed or unblackholed, its client connections
dropped) while `Check`'s clients run.

**The triple:** `MainCluster.spec`'s, with the schedule read-only (`sched ↦*□ steps`, for *every*
list of steps, as the k8s compactor's `MainPartition.spec`): `MainPartition(clients, ops, sched)`
does not panic and returns `Ok` (the check ran: the history is linearizable) or `Unknown` (a step
before the check failed).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Cluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjSpec
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev MainPartition.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.Assumptions] [k8s_io.apimachinery.pkg.runtime.schema.Assumptions]
    [k8s_io.apiserver.pkg.storage.Assumptions] [k8s_io.apiserver.pkg.storage.value.Assumptions]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (clients ops : w64) (sched : GoSlice)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  -- (per-type stage B3) the levels of a thread token the members' gRPC runs use
  srvLevels (GF := GF) →
  cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → storageErrTyOk →
  objTyOk →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      cluster3.startRes (GF := GF) clusterCfg ∗ sched ↦*□ steps ∗ threadTok ∗
      cluster3.premises clusterCfg N id₁ id₂ id₃ ps ctxs boot }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainPartition))
      (Val #clients)) (Val #ops)) (Val #sched))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
