/- Lean-first (no Rocq counterpart).

`c.replica(id)` (cluster.go): replica `id`, or `nil` if there is none (then `id` was not started:
`repKnown` refutes it).
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
abbrev Cluster.replica.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (id : w64),
  {{ isClusterC γr vs c }}
    (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"replica")) (Val #id))
  {{ (r : Loc), RET #r; (⌜r = null⌝ ∗ (repKnown γr id -∗ False)) ∨ isRep γr vs id r }}

end spec

end kvreconf
end EtcdGrove
end Perennial
