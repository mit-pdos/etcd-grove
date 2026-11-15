/-
## `raft.committedEntryInCurrentTerm` (internal)

`stepLeader`, `releasePendingReadIndexMessages`. Mirrors the code (R3's `term`, `zeroTermOnOutOfBounds`; the commit index is at or above the compaction floor, so its term is answered). **Changes.** Over the opened struct (internal layer, `ApiCore.lean`; from `specs-ref`'s
`raft__committedEntryInCurrentTerm.lean`, over `NState`); round 1: the result is stated over the state.
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

/-- (internal) Whether the commit index's entry is of the term. -/
def raft.committedEntryInCurrentTerm.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"committedEntryInCurrentTerm")) (Val #()))
  {{ (b : Bool), RET #b; raftOpen r γ id o ∗ ⌜b = true ↔ o.log.termOf o.log.committed = some o.view.hs.term⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
