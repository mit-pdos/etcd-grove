/- Lean-first (no Rocq counterpart).

`c.Reconfigure(pause, stop)` (reconf.go): random configuration changes proposed at random
replicas until `stop` is closed (a broadcast channel; its closer holds the `Pending` token). Each
change is shaped (`ccTransOk`), so its proposal's persistent atomic update keeps the committed conf
entries shaped (`kvr_ccAu`). Nothing is promised of the outcome.
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
abbrev Cluster.Reconfigure.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (pause : time.Duration) (stop : Loc) (γc : ChanNames),
  {{ isClusterC γr vs c ∗ ownBroadcastChan stop γc iprop(True) .Unknown }}
    (App (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"Reconfigure")) (Val #pause)) (Val #stop))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
