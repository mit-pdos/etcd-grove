/- Lean-first (no Rocq counterpart).

`r.ticker()` (kv.go): ticks the node (`node.Tick`, over `isNode`) at every tick of a
`time.Ticker` of the replica's interval until `stopc` is closed, then stops the ticker and sends on
`tickDone`, with its producer's token (`newReplica` gives it, the stopper has the consumer's).
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
abbrev Replica.ticker.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (ρ : RepNames),
  {{ isReplicaR γr vs id r n st sts ρ ∗ handoffProducer ρ.td false }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"ticker")) (Val #()))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
