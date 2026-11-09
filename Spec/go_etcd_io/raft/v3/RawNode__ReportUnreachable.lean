/-
## `RawNode.ReportUnreachable`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. `node.run` (the matching `node` method's channel case). **Proof sketch.** `raft.tick` or
`raft.Step` of a local message (R2); the result ignored. **Changes.** Unchanged.
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

/-- `RawNode.ReportUnreachable`: keeps the token. -/
def RawNode.ReportUnreachable.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNode rn γ id }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"ReportUnreachable")) (Val #to))
  {{ RET #(); rawNode rn γ id }}

end spec
end Raft
end EtcdGrove
end Perennial
