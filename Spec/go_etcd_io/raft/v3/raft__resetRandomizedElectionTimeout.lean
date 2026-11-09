/-
## `raft.resetRandomizedElectionTimeout` (internal)

`reset`. Mirrors the code: `lockedRand.Intn(electionTimeout)` (positive: `ConfigOk`). **Changes.** Over the opened struct (internal layer, `ApiCore.lean`; from `specs-ref`'s
`raft__resetRandomizedElectionTimeout.lean`, over `NState`); round 1: the result is stated over the state.
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

/-- (internal) A new randomized timeout. -/
def raft.resetRandomizedElectionTimeout.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"resetRandomizedElectionTimeout")) (Val #()))
  {{ RET #(); ∃ t, raftOpen r γ id { o with randomizedElectionTimeout := t } }}

end spec
end Raft
end EtcdGrove
end Perennial
