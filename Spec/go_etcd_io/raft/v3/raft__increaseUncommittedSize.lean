/-
## `raft.increaseUncommittedSize(ents)` (internal)

`appendEntry`. Mirrors the code: refuses only a non-empty payload over a non-empty tail past the
limit. **Changes.** Over `raftCore` (was `NState`'s `uncommittedSize`). **Margin.** The refusal's
condition is not stated.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) Accounts for entries proposed at a leader, or refuses them. -/
def raft.increaseUncommittedSize.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (sl : GoSlice) (dq : DFrac)
    (es : List LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ entryPtrs sl dq es }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"increaseUncommittedSize")) (Val #sl))
  {{ (b : Bool), RET #b; raftCore r γ id ρ ∗ entryPtrs sl dq es }}

end spec
end Raft
end EtcdGrove
end Perennial
