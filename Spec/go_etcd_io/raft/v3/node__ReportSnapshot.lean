/- Lean-first (no Rocq counterpart).

## `node.ReportSnapshot`

The node API's spec. (2026-10-28: moved here from `NodeApiDraft.lean`, where it was drafted over the
API's sealed predicates, now `InvNode.lean`'s; until then this file held the triple over raft's
internals, now the proof's private `node.ReportSnapshot.specRaw`.)
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

/-- **`node.ReportSnapshot(id, status)`**, from any goroutine (the transport's); nothing is
promised. -/
abbrev node.ReportSnapshot.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (to : w64) (status : SnapshotStatus),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReportSnapshot")) (Val #to))
      (Val #status))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
