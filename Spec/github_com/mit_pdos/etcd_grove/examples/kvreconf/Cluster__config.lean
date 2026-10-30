/- Lean-first (no Rocq counterpart).

`c.config(id, st)` (cluster.go): a fresh `*raft.Config` for node `id` on the store's storage `st`,
from the cluster's options (`OptsOk`): what raft's `RestartNode.spec` asks of it (`CfgOk`,
`Config.lean`). For an id that raft accepts (not `0`, not one of the two largest).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Config

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
abbrev Cluster.config.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (id : w64) (st : Loc),
  id ≠ W64 0 → uint.Z id < 2 ^ 64 - 2 →
  {{ isClusterC γr vs c }}
    (App (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"config")) (Val #id)) (Val #st))
  {{ (p : Loc), RET #p; ∃ cv : Config, p ↦ cv ∗ ⌜CfgOk id st cv⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
