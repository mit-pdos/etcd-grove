-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/node__ReportUnreachable.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

## `node.ReportUnreachable`

The node API's spec. (2026-10-28: moved here from `NodeApiDraft.lean`, where it was drafted over the
API's sealed predicates, now `InvNode.lean`'s; until then this file held the triple over raft's
internals, now the proof's private `node.ReportUnreachable.specRaw`.)
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.InvNode

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

/-- **`node.ReportUnreachable(id)`**, from any goroutine (the transport's): a leader's progress of
`id` only; nothing is promised. -/
abbrev node.ReportUnreachable.spec : Prop :=
  ∀ (n : NodeH) (γ : Cluster) (N : Namespace) (id : w64) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id }}
    (App (Val (n.loc @!! go.GoType.PointerType node.ty @!! go!"ReportUnreachable")) (Val #to))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
