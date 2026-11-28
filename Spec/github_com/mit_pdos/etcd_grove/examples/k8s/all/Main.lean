/- Lean-first (no Rocq counterpart).

`Main(k, clients, ops, watchers, wops, sched1, k2, sched2)` (`examples/k8s/all/all.go`;
`notes/k8s-unified-scope.md`, the user's decisions of 2026-11-20; `notes/k8s-compactor-n-plan.md`): the
Kubernetes etcd3 store's partitioned workload on `k` members (`k8setcd3.MainPartition(k, clients, ops,
watchers, wops, sched1)`, on a goroutine) and Kubernetes' compactor under partitions on `k₂` more
members (`compactor.MainPartition(k2, sched2)`, on the main thread), at once; `Main` returns once both have (a
`sync.WaitGroup`). A `holdToken` goroutine, forked first, never returns: its thread token is the one
the store's goroutine exits with (both drivers' triples consume the token they are given).

**The triple:** the two drivers' triples side by side. From the package's `isPkgInit`, the store
cluster's start bundles (each member's data directory and WAL area fresh, its peer and client
addresses free, the peer's HTTP protocol unregistered) and its bridges' addresses free, the
compactor cluster's start bundles and its bridges' addresses free (at `k8s_compactorN.members k₂`), the two
schedules read-only (for *every* two lists of steps), the main thread's token, both clusters' named
premises at one bound `N` and the compactor registry's claims' authority with no endpoint claimed,
`Main` does not panic and returns. The pure premises are the union of the two triples'
(`k8s_etcd3.MainPartition.spec`, `k8s_compactor.MainPartition.spec`): each cluster's boot facts, the
thread and receipt bounds, the server's workload and effect premises, gRPC's method sets,
`errors.As`'s target, the store driver's type facts and the client counts' bounds.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainPartition
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.Assumptions] [k8s_io.apimachinery.pkg.runtime.schema.Assumptions]
    [k8s_io.apiserver.pkg.storage.Assumptions] [k8s_io.apiserver.pkg.storage.value.Assumptions]
    (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (k₂ : Nat) (ids' : List w64) (ps' : List w64) (ctxs' : List (List w8)) (boot' : List LogEntry)
    (clients ops watchers wops : w64) (sched₁ sched₂ : GoSlice)
    (steps₁ steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  srvLevels (GF := GF) →
  1 ≤ k → k ≤ 1000 → ids.length = k →
  k8s_etcd3N.BootFacts ids ps ctxs boot →
  1 ≤ k₂ → k₂ ≤ 1000 → ids'.length = k₂ →
  k8s_compactorN.BootFacts ids' ps' ctxs' boot' →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → k8s_etcd3.storageErrTyOk →
  k8s_etcd3.objTyOk →
  0 ≤ sint.Z clients → 0 ≤ sint.Z watchers → sint.Z clients + sint.Z watchers < 2 ^ 31 →
  0 ≤ sint.Z ops → 0 ≤ sint.Z wops →
  sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.all ∗
      ([∗list] m ∈ k8s_etcd3N.startOf (k8s_etcd3N.members k),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] b ∈ k8s_etcd3N.bridges k, netAddrFree (GF := GF) b) ∗
      ([∗list] m ∈ k8s_etcd3N.startOf (k8s_compactorN.members k₂),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] b ∈ k8s_compactorN.bridges k₂, netAddrFree (GF := GF) b) ∗
      sched₁ ↦*□ steps₁ ∗ sched₂ ↦*□ steps₂ ∗ threadTok ∗
      k8s_etcd3N.premises k N ids ps ctxs boot ∗
      k8s_compactorN.premises k₂ N ids' ps' ctxs' boot' ∗
      k8s.regAuth (∅ : GMap GoString GName) }}
    (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.Main))
      (Val #(W64 k))) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops)) (Val #sched₁))
      (Val #(W64 k₂))) (Val #sched₂))
  {{ RET #(); True }}

end spec

end k8s_all
end EtcdGrove
end Perennial
