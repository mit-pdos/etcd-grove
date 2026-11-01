/- Lean-first (no Rocq counterpart).

`c.restart(id)` (cluster.go): the current incarnation of replica `id` crashed (`Replica.crash`:
`nodeVacant` and the writer's half back), the next one started from the file (`Cluster.start`) and
made current under `c.mu` (the old one's `isReplica` stays: its node stopped). `Crash` runs it,
one at a time: it holds the stopper's share of the current incarnation (`repStop`), and gets the
new one's. `id` is a started one (`repKnown`: `c.replica(id)` is not `nil`, and `Cluster.start`'s
transport needs it).
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
abbrev Cluster.restart.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (id : w64) (r : Loc),
  {{ isClusterC γ vs dir c ∗ kdFileInv γ dir id ∗ repStop γ vs dir id r ∗ repKnown γ id }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"restart")) (Val #id))
  {{ RET #(); ∃ r' : Loc, repStop γ vs dir id r' }}

end spec

end kvdurable
end EtcdGrove
end Perennial
