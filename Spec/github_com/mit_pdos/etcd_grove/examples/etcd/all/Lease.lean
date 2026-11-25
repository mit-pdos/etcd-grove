/- Lean-first (no Rocq counterpart).

`Lease(k4)` (`examples/etcd/all/all.go`; `notes/etcd-unified-scope.md` §3.1): leaseN's `Main(k4)` on a
goroutine of its own (`spawn`) and leasecatchup's `Main()` on the calling thread, at once; `Lease`
returns once both have (a `sync.WaitGroup`).

**The triple:** the two drivers' triples side by side (`etcd_leaseN.Main.spec`,
`etcd_leasecatchup.Main.spec`): from the package's `isPkgInit`, leaseN's members' start bundles and
leasecatchup's cluster's, the calling thread's token and each cluster's named premises at one bound
`N`, `Lease` does not panic and returns; the pure premises are the union of the two triples', once each
where they coincide.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Main
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
abbrev Lease.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (N : Nat)
    (k₄ : Nat) (ids₄ ps₄ : List w64) (ctxs₄ : List (List w8)) (boot₄ : List LogEntry)
    (lid₁ lid₂ lid₃ : w64) (psL : List w64) (ctxsL : List (List w8)) (bootL : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  srvLevels (GF := GF) →
  1 ≤ k₄ → k₄ ≤ 1000 → ids₄.length = k₄ → etcd_putgetN.BootFacts ids₄ ps₄ ctxs₄ boot₄ →
  cluster3.BootFacts lid₁ lid₂ lid₃ psL ctxsL bootL →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk → lease.leasesNoExpiry →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all ∗
      ([∗list] m ∈ etcd_leaseN.startOf (etcd_leaseN.members k₄),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      cluster3.startRes (GF := GF) etcd_leasecatchup.clusterCfg ∗
      threadTok ∗
      etcd_leaseN.premises k₄ N ids₄ ps₄ ctxs₄ boot₄ ∗
      cluster3.premises etcd_leasecatchup.clusterCfg N lid₁ lid₂ lid₃ psL ctxsL bootL }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.Lease)) (Val #(W64 k₄)))
  {{ RET #(); True }}

end spec

end etcd_all
end EtcdGrove
end Perennial
