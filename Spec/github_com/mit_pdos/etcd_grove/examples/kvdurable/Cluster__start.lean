/- Lean-first (no Rocq counterpart).

`c.start(id)` (cluster.go): an incarnation of replica `id` from its file: `durable.Read` (the file's
invariant: its contents `o`, which the writer's half held here names), `openStorage` (an empty
storage if there is no file), the stored snapshot's state decoded (its certificate, `kdSnapCert`),
`Config.Applied` chosen at random from the log's start to the snapshot's index (or `0`), then
`RestartNode` (from the id's slot, `nodeVacant`; its update fires over the file's invariant, whose
durable state the storage holds: `StorageHolds S (kdContents o)`; at the configuration point the
snapshot's index, `confAt γ a m`), and `newReplica`, its transport `c.sender(id)` (for a started
`id`, `repKnown`: each send looks its sender up by id, `c.replica(id)`). The writer's half goes to
the new incarnation's `dmu`.
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
abbrev Cluster.start.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (id : w64) (S : RaftState)
    (o : Option StorFile),
  1 ≤ uint.nat id → uint.nat id ≤ 9 →
  {{ isClusterC γ vs dir c ∗ kdFileInv γ dir id ∗ nodeVacant γ.r.cluster id ∗
      kdWriter γ id S o ∗ repKnown γ id }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"start")) (Val #id))
  {{ (r : Loc), RET #r; (∃ (n st sts sq : Loc) (ρ : KdRepNames),
        isReplicaR γ vs dir id r n st sts sq ρ) ∗ repStop γ vs dir id r }}

end spec

end kvdurable
end EtcdGrove
end Perennial
