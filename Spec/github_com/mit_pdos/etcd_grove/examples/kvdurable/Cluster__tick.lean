/- Lean-first (no Rocq counterpart).

`c.tick()` (cluster.go): a positive tick interval (what `newReplica` takes).
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
abbrev Cluster.tick.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc),
  {{ isClusterC γ vs dir c }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"tick")) (Val #()))
  {{ (d : time.Duration), RET #d; ⌜0 < sint.Z d⌝ }}

end spec

end kvdurable
end EtcdGrove
end Perennial
