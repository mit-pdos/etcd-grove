/- Lean-first (no Rocq counterpart).

## `node.Step(ctx, m)` (node.go:473)

A message from the network, from any goroutine: `step` of it, on `recvc`, which `run` steps
as `RawNode.Step` does (`netP`: what `RawNode.Step` takes, and a term within the budget).
A local message not from a local target is ignored (since 2026-10-13 `netP` admits two
local types, `MsgUnreachable` and `MsgSnapStatus`, the reports `node.go` itself puts on
`recvc`: through `Node.Step` they are ignored unless from a local target).
Since 2026-10-10 also a proposal forwarded by a peer (`fwdP`, `stepP`): a follower's
`Ready` holds the proposals it forwards to the leader (each entry's data deposited by the
proposing node), which `step` hands to `run` on `propc`.
Specified for `context.Background()`.
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
abbrev node.Step.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (m : raftpb.Message),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗ stepP γ id m }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Step"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #m))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
