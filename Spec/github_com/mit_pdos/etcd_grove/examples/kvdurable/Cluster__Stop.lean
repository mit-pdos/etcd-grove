/- Lean-first (no Rocq counterpart). kvreconf's, with the crasher's token for the stopper's.

`c.Stop()` (cluster.go): stops every replica's current incarnation. With the crasher's token, which
`c.all()` leaves in the lock (`Cluster.all.specStop`): no restart is under way, none can start, and
`all` takes every incarnation's `repStop` out of the lock.
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
abbrev Cluster.Stop.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc),
  {{ isClusterC γ vs dir c ∗ crasher γ }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
