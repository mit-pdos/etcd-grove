/-
## `raft.promotable` (internal)

`hup`, `tickElection`, `campaign`. Mirrors the code (R3's `hasNextOrInProgressSnapshot`). **Changes.** Over the opened struct (internal layer, `ApiCore.lean`; from `specs-ref`'s
`raft__promotable.lean`, over `NState`); round 1: the result is stated over the state.
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

/-- (internal) Whether the node may campaign: a progress, no learner, no snapshot pending. -/
def raft.promotable.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"promotable")) (Val #()))
  {{ (b : Bool), RET #b; raftOpen r γ id o ∗ ⌜b = decide ((o.view.prs !! id).isSome ∧ o.isLearner = false ∧ o.log.us.snap = none)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
