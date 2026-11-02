/- Lean-first (no Rocq counterpart).

`r.run(send)` (kv.go): the replica's loop, handling the node's `Ready`s until `stopc` is closed
(or a `Ready` would take the log past `maxIndex`, which does not happen), then sending the loop's
`nodeRunning 1` on `runDone`. It starts from `runStart` (the node just started, the replicated state
empty), with `send` the replica's transport (`sendSpec`). Nothing is promised of its end: the loop's
results are the store invariant's (every committed entry applied in order at every replica, each
waiter answered by `waitP`/`readAns`).
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
abbrev Replica.run.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (ρ : RepNames) (f : GoFunc),
  {{ isReplicaR γr vs id r n st sts ρ ∗ runStart γr vs id r n st ρ ∗ sendSpec γr id f }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"run")) (Val #f))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
