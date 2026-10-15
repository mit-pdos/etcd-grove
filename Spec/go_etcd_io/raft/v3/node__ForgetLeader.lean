/- Lean-first (no Rocq counterpart).

## `node.ForgetLeader(ctx)` (node.go:604), 2026-10-13

From any goroutine: `step` of `pb.Message{Type: MsgForgetLeader}` (`netP_local`), which
`run` steps as `RawNode.ForgetLeader` does: a follower forgets its leader. Specified for
`context.Background()`. The error says only whether the message reached `run`.
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
abbrev node.ForgetLeader.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ForgetLeader"))
      (Val #(interface.ok context.backgroundCtxVal)))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
