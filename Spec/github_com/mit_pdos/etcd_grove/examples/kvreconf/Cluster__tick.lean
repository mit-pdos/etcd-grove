/- Lean-first (no Rocq counterpart).

`c.tick()` (cluster.go): a positive tick interval.
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
abbrev Cluster.tick.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc),
  {{ isClusterC γr vs c }}
    (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"tick")) (Val #()))
  {{ (d : time.Duration), RET #d; ⌜0 < sint.Z d⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
