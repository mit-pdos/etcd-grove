/- Lean-first (no Rocq counterpart).
`r.snapshotter()` (kv.go; kvreconf-snapshot-thread, 2026-10-30): the snapshot goroutine, taking
`run`'s requests from `snapc` (`snapshot`) until `stopc` is closed, then sending on `snapDone` (its
producer's token).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- See the file header. -/
abbrev Replica.snapshotter.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (ρ : RepNames),
  {{ isReplicaR γr vs id r n st sts ρ ∗ handoffProducer ρ.sd false }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"snapshotter")) (Val #()))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
