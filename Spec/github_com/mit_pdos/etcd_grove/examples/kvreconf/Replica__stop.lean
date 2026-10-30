/- Lean-first (no Rocq counterpart).

`r.stop()` (kv.go): closes `stopc`, waits for the loop (which hands back `nodeRunning 1` on
`runDone`), the clock and the snapshot goroutine, and stops the node. It takes the stopper's share of the replica
(`repStop`): `stopc` is closed once.
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
abbrev Replica.stop.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (r : Loc),
  {{ repStop γr vs r }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"stop")) (Val #()))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
