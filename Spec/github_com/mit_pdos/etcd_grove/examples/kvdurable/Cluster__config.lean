/- Lean-first (no Rocq counterpart).

`c.config(id, st, applied)` (cluster.go): a fresh `*raft.Config` for node `id` on the store's storage
`st`, restarted at the applied index `applied`, from the cluster's options (`kdOptsOk`): what raft's
`RestartNode.spec` asks of it (`kdCfgOk`, `Config.lean`; `Applied` is `applied`, which
`RestartNode.spec` bounds). For an id that raft accepts (not `0`, not one of the two largest).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Config

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
abbrev Cluster.config.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (id : w64) (st : Loc) (applied : w64),
  id ≠ W64 0 → uint.Z id < 2 ^ 64 - 2 →
  {{ isClusterC γ vs dir c }}
    (App (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"config")) (Val #id))
      (Val #st)) (Val #applied))
  {{ (p : Loc), RET #p; ∃ cv : Config, p ↦ cv ∗ ⌜kdCfgOk id st applied cv⌝ }}

end spec

end kvdurable
end EtcdGrove
end Perennial
