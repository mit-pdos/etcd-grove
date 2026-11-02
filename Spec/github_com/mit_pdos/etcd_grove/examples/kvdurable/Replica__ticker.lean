/- Lean-first (no Rocq counterpart). kvreconf's (the same Go text), ported.

`r.ticker()` (kv.go): ticks the node (`node.Tick`, over `isNode`) at every tick of a
`time.Ticker` of the replica's interval until `stopc` is closed, then stops the ticker and sends on
`tickDone`, with its producer's token (`newReplica` gives it, the stopper has the consumer's).
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
abbrev Replica.ticker.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq : Loc) (ρ : KdRepNames),
  {{ isReplicaR γ vs dir id r n st sts sq ρ ∗ handoffProducer ρ.td false }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"ticker")) (Val #()))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
