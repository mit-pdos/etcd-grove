-- The copy for the part `RaftNoAx/` of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Cluster__Disrupt.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). kvreconf's.

`c.Disrupt(pause, stop)` (reconf.go): random leadership transfers, campaigns and forgotten leaders
at random replicas until `stop` is closed. Nothing is promised of the outcome.
-/
module

public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Cluster.Disrupt.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (pause : time.Duration) (stop : Loc)
    (γc : ChanNames),
  {{ isClusterC (GF := GF) γ vs dir c ∗ ownBroadcastChan stop γc iprop(True) .Unknown }}
    (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"Disrupt")) (Val #pause)) (Val #stop))
  {{ RET #(); True }}

end spec

end raft_kvdurable
end EtcdGrove
end Perennial
