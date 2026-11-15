/-
## `raft.hasLeader()`

**Users.** `node.run` (`node.go:368`: whether to take proposals). **Proof sketch.** Reads `lead`.
**Changes.** Over the view. **Margin.** Exact.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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

/-- Whether the view has a leader. -/
def raft.hasLeader.spec : Prop :=
  ∀ (r : Loc) (id : w64) (ρ : CoreView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftRO r id ρ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"hasLeader")) (Val #()))
  {{ (b : Bool), RET #b; raftRO r id ρ ∗ ⌜b = decide (ρ.lead ≠ W64 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
