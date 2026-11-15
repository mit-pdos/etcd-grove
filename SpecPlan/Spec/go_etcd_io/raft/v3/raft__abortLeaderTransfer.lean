/-
## `raft.abortLeaderTransfer` (internal)

`reset`, `tickHeartbeat`, `stepLeader`, `switchToConfig`. Mirrors the code. **Changes.** Over the opened struct (internal layer, `ApiCore.lean`; from `specs-ref`'s
`raft__abortLeaderTransfer.lean`, over `NState`); round 1: the result is stated over the state.
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

/-- (internal) Abandons a leader transfer. -/
def raft.abortLeaderTransfer.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"abortLeaderTransfer")) (Val #()))
  {{ RET #(); raftOpen r γ id { o with leadTransferee := W64 0 } }}

end spec
end Raft
end EtcdGrove
end Perennial
