/-
## `node.TransferLeadership(ctx, lead, transferee)`

**Users.** etcd's `EtcdServer.MoveLeader`/`TransferLeadership` (`server.go:1285`); the examples'
disruptions (`kvdurable/reconf.go:114`). Snippet: `readyloop.go` (`ReqDisrupt`).

**Proof sketch.** A local `MsgTransferLeader` (from the transferee, to `lead`) on `recvc` (a local
message: no `msgSent` needed; the leader's `stepLeader` checks the transferee, R2), or `done`, or
`ctx`.

**Changes.** Unchanged. **Margin.** Nothing is said of whether leadership moved.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- **Asks for a leader transfer** (any ids). -/
def node.TransferLeadership.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterface)
    (lead transferee : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ Context.ctxOk ctx }}
    (App (App (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"TransferLeadership")) (Val #ctx)) (Val #lead))
      (Val #transferee))
  {{ RET #(); True }}

end spec
end Raft
end EtcdGrove
end Perennial
