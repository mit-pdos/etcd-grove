/- Lean-first (no Rocq counterpart).

`r.snapshotter(known)` (kv.go): the snapshot goroutine, until `stopc` is closed: each request
(`snapReqOk`) handed to `snapshot`; then its half of `nodeRunning` (which its `persist` uses to fire
a pending *enter*) on `snapDone`. `known` is a lower bound of the stored snapshot's index (the `MemoryStorage`'s and the image's).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Replica.snapshotter.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq : Loc)
    (ρ : KdRepNames) (known : w64),
  {{ isReplicaR γ vs dir id r n st sts sq ρ ∗ handoffProducer ρ.sd false ∗
      memSnapLb ρ.γs (uint.nat known) ∗ monoNatLbOwn ρ.ph.is (uint.nat known) ∗ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"snapshotter")) (Val #known))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
