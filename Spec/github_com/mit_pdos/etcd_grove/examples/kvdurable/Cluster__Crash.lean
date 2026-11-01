/- Lean-first (no Rocq counterpart).

`c.Crash(pause, stop)` (reconf.go): until `stop` is closed, a random replica restarted
(`Cluster.restart`), at random times. One `Crash` runs at a time: it holds the cluster's crasher
token (the stopper shares of the current incarnations, which it moves to the new ones).
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
abbrev Cluster.Crash.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (pause : time.Duration) (stop : Loc)
    (γst : ChanNames),
  {{ isClusterC γ vs dir c ∗ ownBroadcastChan stop γst iprop(True) .Unknown }}
    (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"Crash")) (Val #pause)) (Val #stop))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
