/- Lean-first (no Rocq counterpart).

`KV(k1, clients, ops, sched1, nw, nops, sched2, cnw, cnops)` (`examples/etcd/all/all.go`;
`notes/etcd-unified-scope.md` §3.1): txnlinfaultsN's `Main(k1, clients, ops, sched1)`, partition's
`MainWatch(nw, nops, sched2)`, compactwatch's `Main()` and compacted's `Main()`, each on a goroutine of its
own (`spawn`), and cache's `Main(cnw, cnops)` on the calling thread, at once; `KV` returns once all have
(a `sync.WaitGroup`).

**The triple:** the five drivers' triples side by side. From the package's `isPkgInit`, each cluster's
start bundles (txnlinfaultsN's `k₁` members' and bridges', partition's cluster's, the three
one-member clusters' members'), the two schedules read-only, the calling thread's token and each
cluster's named premises at one bound `N`, `KV` does not panic and returns. The pure premises are the
union of the five triples' (`etcd_txnlinfaultsN.Main.spec`, `etcd_partition.MainWatch.spec`,
`etcd_compactwatch.Main.spec`, `etcd_compacted.Main.spec`, `etcd_cache.Main.spec`), once each where
they coincide; the thread and receipt bounds as instances (as `k8s_all.Main.spec`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.MainWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.compactwatch.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.compacted.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

/-- See the file header. -/
abbrev KV.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (N : Nat)
    (k₁ : Nat) (ids₁ ps₁ : List w64) (ctxs₁ : List (List w8)) (boot₁ : List LogEntry)
    (pid₁ pid₂ pid₃ : w64) (psP : List w64) (ctxsP : List (List w8)) (bootP : List LogEntry)
    (cwId : w64) (ctxsCW : List (List w8)) (bootCW : List LogEntry)
    (cId : w64) (ctxsC : List (List w8)) (bootC : List LogEntry)
    (kvId : w64) (ctxsK : List (List w8)) (bootK : List LogEntry)
    (clients ops nw nops cnw cnops : w64) (sched₁ sched₂ : GoSlice)
    (steps₁ steps₂ : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  srvLevels (GF := GF) →
  1 ≤ k₁ → k₁ ≤ 1000 → ids₁.length = k₁ →
  etcd_txnlinfaultsN.BootFacts ids₁ ps₁ ctxs₁ boot₁ →
  etcd_partition.BootFacts pid₁ pid₂ pid₃ psP ctxsP bootP →
  etcd_compactwatch.BootFacts cwId ctxsCW bootCW →
  etcd_compacted.BootFacts cId ctxsC bootC →
  etcd_putget.BootFacts kvId ctxsK bootK →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  0 ≤ sint.Z nw → sint.Z nw < 2 ^ 31 → 0 ≤ sint.Z nops → sint.Z nw * sint.Z nops < 2 ^ 62 →
  0 ≤ sint.Z cnw → sint.Z cnw < 2 ^ 31 → 0 ≤ sint.Z cnops → sint.Z cnw * sint.Z cnops < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all ∗
      ([∗list] m ∈ etcd_txnlinfaultsN.startOf (etcd_txnlinfaultsN.members k₁),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] b ∈ etcd_txnlinfaultsN.bridges k₁, netAddrFree (GF := GF) b) ∗
      cluster3.startRes (GF := GF) etcd_partition.clusterCfg ∗
      etcdstart.memberStartRes (GF := GF) go!"compactkv" ⟨none, some go!"127.0.0.1:23794"⟩ ∗
      etcdstart.memberStartRes (GF := GF) go!"putgetc" ⟨none, some go!"127.0.0.1:23791"⟩ ∗
      etcdstart.memberStartRes (GF := GF) go!"cachekv" ⟨none, some go!"127.0.0.1:23873"⟩ ∗
      sched₁ ↦*□ steps₁ ∗ sched₂ ↦*□ steps₂ ∗ threadTok ∗
      etcd_txnlinfaultsN.premises k₁ N ids₁ ps₁ ctxs₁ boot₁ ∗
      etcd_partition.premises N pid₁ pid₂ pid₃ psP ctxsP bootP ∗
      etcd_compactwatch.premises N cwId ctxsCW bootCW ∗
      etcd_compacted.premises N cId ctxsC bootC ∗
      etcd_cache.premises N kvId ctxsK bootK }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.KV))
      (Val #(W64 k₁))) (Val #clients)) (Val #ops)) (Val #sched₁)) (Val #nw)) (Val #nops))
      (Val #sched₂)) (Val #cnw)) (Val #cnops))
  {{ RET #(); True }}

end spec

end etcd_all
end EtcdGrove
end Perennial
