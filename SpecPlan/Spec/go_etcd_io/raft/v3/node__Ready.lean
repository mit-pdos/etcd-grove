/-
## `node.Ready()`

**Users.** etcd's `raftNode.start` (`raft.go:189`, `case rd := <-r.Ready()` in a `select` with the
ticker and `stopped`); every example's run loop. Snippet: `readyloop.go`.

**Proof sketch.** Returns the `readyc` field: `isNode`'s invariant knows it. What a receive gives is
`readyChan_recv.spec` (`Api.lean`).

**Changes.** Unchanged.
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

/-- **The `Ready` channel** of node `n`. -/
def node.Ready.spec : Prop :=

  ∀ (n : Loc) (γ : Cluster) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ id }}
    (App (Val (n @!! go.GoType.PointerType go_etcd_io.raft.v3.node.ty @!! go!"Ready")) (Val #()))
  {{ (ch : Loc), RET #ch; isReadyChan n ch }}

end spec
end Raft
end EtcdGrove
end Perennial
