/- Lean-first (no Rocq counterpart). kvreconf's.

`c.Disrupt(pause, stop)` (reconf.go): random leadership transfers, campaigns and forgotten leaders
at random replicas until `stop` is closed. Nothing is promised of the outcome.
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
abbrev Cluster.Disrupt.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (pause : time.Duration) (stop : Loc)
    (γc : ChanNames),
  {{ isClusterC γ vs dir c ∗ ownBroadcastChan stop γc iprop(True) .Unknown }}
    (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"Disrupt")) (Val #pause)) (Val #stop))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
