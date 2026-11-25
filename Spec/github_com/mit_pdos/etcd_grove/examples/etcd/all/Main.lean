/- Lean-first (no Rocq counterpart).

`Main(k1, clients, ops, sched1, nw, nops, sched2, cnw, cnops, k2, k3, k4, k5)` (`examples/etcd/all/all.go`;
`notes/etcd-unified-scope.md` §3.1): the four parts `KV`, `Auth` and `Lease`, each on a goroutine of its
own (`spawn`), and `Restart` on the main thread, at once; `Main` returns once all have (a
`sync.WaitGroup`).

**The triple:** the four parts' triples side by side (`KV.spec`, `Auth.spec`, `Lease.spec`,
`Restart.spec`): from the package's `isPkgInit`, the eleven clusters' start bundles, the two schedules
read-only, the main thread's token and each cluster's named premises at one bound `N`, `Main` does not
panic and returns; the pure premises are the union of the four triples', once each where they coincide.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.KV
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Auth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Lease
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Restart

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
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (N : Nat)
    (k₁ : Nat) (ids₁ ps₁ : List w64) (ctxs₁ : List (List w8)) (boot₁ : List LogEntry)
    (pid₁ pid₂ pid₃ : w64) (psP : List w64) (ctxsP : List (List w8)) (bootP : List LogEntry)
    (cwId : w64) (ctxsCW : List (List w8)) (bootCW : List LogEntry)
    (cId : w64) (ctxsC : List (List w8)) (bootC : List LogEntry)
    (kvId : w64) (ctxsK : List (List w8)) (bootK : List LogEntry)
    (k₂ : Nat) (ids₂ ps₂ : List w64) (ctxs₂ : List (List w8)) (boot₂ : List LogEntry)
    (k₃ : Nat) (ids₃ ps₃ : List w64) (ctxs₃ : List (List w8)) (boot₃ : List LogEntry)
    (k₄ : Nat) (ids₄ ps₄ : List w64) (ctxs₄ : List (List w8)) (boot₄ : List LogEntry)
    (lid₁ lid₂ lid₃ : w64) (psL : List w64) (ctxsL : List (List w8)) (bootL : List LogEntry)
    (k₅ : Nat) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8)) (boot₅ : List LogEntry)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
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
  1 ≤ k₂ → k₂ ≤ 1000 → ids₂.length = k₂ → etcd_putgetN.BootFacts ids₂ ps₂ ctxs₂ boot₂ →
  1 ≤ k₃ → k₃ ≤ 1000 → ids₃.length = k₃ → etcd_putgetN.BootFacts ids₃ ps₃ ctxs₃ boot₃ →
  leaseIdsApart ids₃ →
  1 ≤ k₄ → k₄ ≤ 1000 → ids₄.length = k₄ → etcd_putgetN.BootFacts ids₄ ps₄ ctxs₄ boot₄ →
  cluster3.BootFacts lid₁ lid₂ lid₃ psL ctxsL bootL →
  k₅ ≤ 1000 → ids₅.length = k₅ → etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅ →
  etcd_restart1.BootFacts rId ctxsR bootR →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk → lease.leasesNoExpiry →
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
      ([∗list] m ∈ etcd_authN.startOf (etcd_authN.members k₂),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] m ∈ etcd_authlease.startOf (etcd_authlease.members k₃),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] m ∈ etcd_leaseN.startOf (etcd_leaseN.members k₄),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      cluster3.startRes (GF := GF) etcd_leasecatchup.clusterCfg ∗
      ([∗list] m ∈ etcd_restartN.members k₅,
        etcdstart.memberStartRes (GF := GF) m.Name' ⟨some m.Peer', none⟩) ∗
      etcdstart.memberStartRes (GF := GF) etcd_restart1.name {} ∗
      sched₁ ↦*□ steps₁ ∗ sched₂ ↦*□ steps₂ ∗ threadTok ∗
      etcd_txnlinfaultsN.premises k₁ N ids₁ ps₁ ctxs₁ boot₁ ∗
      etcd_partition.premises N pid₁ pid₂ pid₃ psP ctxsP bootP ∗
      etcd_compactwatch.premises N cwId ctxsCW bootCW ∗
      etcd_compacted.premises N cId ctxsC bootC ∗
      etcd_cache.premises N kvId ctxsK bootK ∗
      etcd_authN.premises k₂ N ids₂ ps₂ ctxs₂ boot₂ ∗
      etcd_authlease.premises k₃ N ids₃ ps₃ ctxs₃ boot₃ ∗
      etcd_leaseN.premises k₄ N ids₄ ps₄ ctxs₄ boot₄ ∗
      cluster3.premises etcd_leasecatchup.clusterCfg N lid₁ lid₂ lid₃ psL ctxsL bootL ∗
      etcd_restartN.premises k₅ N ids₅ ps₅ ctxs₅ boot₅ ∗
      etcd_restart1.premises N rId ctxsR bootR }}
    (App (App (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.Main))
      (Val #(W64 k₁))) (Val #clients)) (Val #ops)) (Val #sched₁)) (Val #nw)) (Val #nops))
      (Val #sched₂)) (Val #cnw)) (Val #cnops))
      (Val #(W64 k₂))) (Val #(W64 k₃))) (Val #(W64 k₄))) (Val #(W64 k₅)))
  {{ RET #(); True }}

end spec

end etcd_all
end EtcdGrove
end Perennial
