/- Lean-first (no Rocq counterpart).

`Auth(k2, k3)` (`examples/etcd/all/all.go`; `notes/etcd-unified-scope.md` §3.1): authN's `Main(k2)` on a
goroutine of its own (`spawn`) and authlease's `Main(k3)` on the calling thread, at once; `Auth` returns
once both have (a `sync.WaitGroup`).

**The triple:** the two drivers' triples side by side (`etcd_authN.Main.spec`,
`etcd_authlease.Main.spec`): from the package's `isPkgInit`, each cluster's members' start bundles,
the calling thread's token and each cluster's named premises at one bound `N`, `Auth` does not panic
and returns; the pure premises are the union of the two triples', once each where they coincide.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Main
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
abbrev Auth.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (N : Nat)
    (k₂ : Nat) (ids₂ ps₂ : List w64) (ctxs₂ : List (List w8)) (boot₂ : List LogEntry)
    (k₃ : Nat) (ids₃ ps₃ : List w64) (ctxs₃ : List (List w8)) (boot₃ : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  srvLevels (GF := GF) →
  1 ≤ k₂ → k₂ ≤ 1000 → ids₂.length = k₂ → etcd_putgetN.BootFacts ids₂ ps₂ ctxs₂ boot₂ →
  1 ≤ k₃ → k₃ ≤ 1000 → ids₃.length = k₃ → etcd_putgetN.BootFacts ids₃ ps₃ ctxs₃ boot₃ →
  leaseIdsApart ids₃ →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk → lease.leasesNoExpiry →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all ∗
      ([∗list] m ∈ etcd_authN.startOf (etcd_authN.members k₂),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] m ∈ etcd_authlease.startOf (etcd_authlease.members k₃),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      threadTok ∗
      etcd_authN.premises k₂ N ids₂ ps₂ ctxs₂ boot₂ ∗
      etcd_authlease.premises k₃ N ids₃ ps₃ ctxs₃ boot₃ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.Auth))
      (Val #(W64 k₂))) (Val #(W64 k₃)))
  {{ RET #(); True }}

end spec

end etcd_all
end EtcdGrove
end Perennial
