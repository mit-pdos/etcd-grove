/-
## `node.ForgetLeader(ctx)`

**Users.** the examples' disruptions (`kvdurable/reconf.go:118`); etcd does not call it. Snippet: `readyloop.go` (`ReqDisrupt`).

**Proof sketch.** `n.step(ctx, MsgForgetLeader)` (`stepOk` of a local `MsgForgetLeader`: needs nothing); the run
goroutine steps it (`raft.Step`: R2's spec, which keeps raft's invariants for any local message).

**Changes.** Unchanged (over opaque predicates). **Margin.** The error says only how the hand-off
ended, not what raft did.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

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

/-- **Asks node `n` to forget its leader** (a `MsgForgetLeader`); the error is the hand-off's. -/
def node.ForgetLeader.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id ∗ Context.ctxOk ctx }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"ForgetLeader")) (Val #ctx))
  {{ (err : GoInterface), RET #err; nodeErr n ctx err }}

end spec
end Raft
end EtcdGrove
end Perennial
