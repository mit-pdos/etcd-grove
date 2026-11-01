/- Lean-first (no Rocq counterpart).

## `node.Stop()` (node.go:331)

The node API's spec (2026-10-29, stage U9a).
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.Stop()`**, by the holder of the whole of the node's liveness (`nodeRunning n γ N 1`),
which it gives up: the node stops (its `run` returns), and `Stop` returns once it has
(`nodeStopped`). -/
abbrev node.Stop.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
      nodeRunning n γ N 1 }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); nodeStopped n γ N }}

end spec

end EtcdGrove
end Perennial
