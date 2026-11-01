/- Lean-first (no Rocq counterpart).

## `node.Status()` (node.go:575)

The node API's spec (2026-10-29, stage U7): the caller gets a `Status` value whose memory is its own
(`statusOwn`). The proof's raw triple, `node.Status.specRaw`, is over `isNodeChan`.
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

/-- **`node.Status()`**, from any goroutine: the node's status, a copy (`run` answers on a fresh
channel with `getStatus`), or `Status{}` once the node stopped; its memory the caller's
(`statusOwn`). Nothing is promised of the values. -/
abbrev node.Status.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Status")) (Val #()))
  {{ (st : Status), RET #st; statusOwn st }}

end spec

end EtcdGrove
end Perennial
