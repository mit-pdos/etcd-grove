/- Lean-first (no Rocq counterpart).

`c.fileOf(id)` (cluster.go): the file of replica `id` in the cluster's directory `dir`
(`kdFileName dir id`: `dir + "/replica-" + itoa(id)`), the name its file invariant (`kdFileInv`) is
about.
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
abbrev Cluster.fileOf.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (id : w64),
  {{ isClusterC γ vs dir c }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"fileOf")) (Val #id))
  {{ RET #(kdFileName dir id); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
