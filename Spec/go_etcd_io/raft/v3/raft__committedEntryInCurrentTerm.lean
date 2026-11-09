/-
## `raft.committedEntryInCurrentTerm` (internal)

`stepLeader`, `releasePendingReadIndexMessages`. Mirrors the code (R3's `term`, `zeroTermOnOutOfBounds`). **Changes.** Over `raftCore` (from `specs-ref`'s `raft__committedEntryInCurrentTerm.lean`, over `NState`).
**Margin.** The result is not related to the view.
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

/-- (internal) Whether the commit index's entry is of the term. -/
def raft.committedEntryInCurrentTerm.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"committedEntryInCurrentTerm")) (Val #()))
  {{ (b : Bool), RET #b; raftCore r γ id ρ }}

end spec
end Raft
end EtcdGrove
end Perennial
