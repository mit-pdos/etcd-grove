/-
## `RawNode.BasicStatus()`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token. **Proof sketch.** `getBasicStatus(r)` (R2's raft predicates). **Changes.** Unchanged.
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

/-- `RawNode.BasicStatus`: the id; a hard state (fresh). -/
def RawNode.BasicStatus.spec : Prop :=

  ∀ (rn : Loc) (γ : Cluster) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNode rn γ id }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"BasicStatus")) (Val #()))
  {{ (bs : go_etcd_io.raft.v3.BasicStatus), RET #bs; rawNode rn γ id ∗ ⌜bs.ID' = id⌝ ∗
      ∃ hs, hsPtr bs.HardState' hs }}

end spec
end Raft
end EtcdGrove
end Perennial
