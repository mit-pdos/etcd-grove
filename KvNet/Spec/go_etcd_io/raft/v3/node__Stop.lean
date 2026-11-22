-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/node__Stop.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

## `node.Stop()` (node.go:331)

The node API's spec (2026-10-29, stage U9a).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvNode

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
(`nodeStopped`), with the node's id vacant again (`nodeVacant`, 2026-11-01, durability stage I-7;
stage II (n): `Stop` gives it back itself, from `run`'s answer on `stop`), for a restart.
(2026-11-21, the crash invariant) The vacancy comes back armed (`nodeVacantA`), at the arm the node
was started from (`nodeArm`, which `StartNode`/`RestartNode` gave: `nodeArm_agree`). -/
abbrev node.Stop.spec : Prop :=
  ∀ (n : NodeH) (γ : Cluster) (N : Namespace) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗
      nodeRunning n γ N 1 }}
    (App (Val (n.loc @!! go.GoType.PointerType node.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); nodeStopped n γ N ∗ ∃ x, nodeVacantA γ id x ∗ nodeArm n γ x }}

end spec

end EtcdGrove
end Perennial
