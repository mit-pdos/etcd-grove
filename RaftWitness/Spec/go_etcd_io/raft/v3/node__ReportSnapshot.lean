/- Lean-first (no Rocq counterpart).

## `node.ReportSnapshot(id, status)` (node.go:586), 2026-10-13

From any goroutine: `pb.Message{Type: MsgSnapStatus, From: id, Reject: status ==
SnapshotFailure}` onto `recvc` (`netP_local`), which `run` steps as
`RawNode.ReportSnapshot` does: a leader's `Progress` of `id` only. `n.done` never fires.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.ReportSnapshot.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (to : w64) (st : SnapshotStatus),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReportSnapshot")) (Val #to))
      (Val #st))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
