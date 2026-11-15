/- Lean-first (no Rocq counterpart).

`MainCluster(clients, ops)` (`examples/k8s/etcd3/k8setcd3.go`; step 1 of "k8s etcd3 over cluster3" in
`notes/k8s-etcd3-plan.md`, 2026-11-06): `Main` over a three-member cluster. The cluster
(`cluster3.StartCluster` at `clusterCfg`, compaction off), a kubernetes client of the three members'
bridges configured as etcd's clients are in practice (`etcdstart`'s dial and keepalive timeouts, the
default retries), the seed keys (`seed`), the Kubernetes etcd3 store over the client (`etcd3.New`, as
`Main`'s) and `Check(s, st0, clients, ops, 0)`, with a panic if porcupine reports the history
`Illegal`.

**The triple:** from the package's `isPkgInit`, the cluster's start bundle (`cluster3.startRes`: each
member's WAL directory fresh, its peer and client addresses free, the peer's HTTP protocol
unregistered, the bridges' addresses free), the main thread's token and the cluster's named premises
(`cluster3.premises` at `clusterCfg`), `MainCluster(clients, ops)` does not panic and returns `Ok`
(the check ran: the history is linearizable) or `Unknown` (a step before the check failed). The pure
premises are `Main`'s (`Main.spec`), with the cluster's boot facts (`cluster3.BootFacts`) for the one
member's (`etcd_putget.BootFacts`), as the k8s compactor's `MainPartition` takes them. The bounds the
adequacy theorem fixes (`threadBound`, `receiptBound`) are instance binders (`ThreadBoundLe`,
`ReceiptBoundLe`), the form `notes/bounds-plan.md` prefers (as `examples/etcd/restart`'s `Main.spec`),
not `Main.spec`'s premises.
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
abbrev MainCluster.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.Assumptions] [k8s_io.apimachinery.pkg.runtime.schema.Assumptions]
    [k8s_io.apiserver.pkg.storage.Assumptions] [k8s_io.apiserver.pkg.storage.value.Assumptions]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (clients ops : w64)
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
      cluster3.startRes (GF := GF) clusterCfg ∗ threadTok ∗
      cluster3.premises clusterCfg N id₁ id₂ id₃ ps ctxs boot }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainCluster)) (Val #clients))
      (Val #ops))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
