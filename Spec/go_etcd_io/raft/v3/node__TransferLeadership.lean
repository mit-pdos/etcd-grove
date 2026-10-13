/- Lean-first (no Rocq counterpart).

## `node.TransferLeadership(ctx, lead, transferee)` (node.go:595), 2026-10-13

From any goroutine: `pb.Message{Type: MsgTransferLeader, From: transferee, To: lead}` onto
`recvc` (`netP`: unstamped, no entries, no context; `netP_local`), which `run` steps as
`RawNode.TransferLeader` does: at a follower forwarded to its leader, at a leader recorded
with a `MsgTimeoutNow` or an append to the transferee. Specified for
`context.Background()`; `n.done` never fires. Nothing is promised of the transfer.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Perennial.Proof.context

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
abbrev node.TransferLeadership.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (lead transferee : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n }}
    (App (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"TransferLeadership"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #lead)) (Val #transferee))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
