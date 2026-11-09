/-
## `raft.reduceUncommittedSize` (internal)

`raft.Step` (apply acknowledgements). Mirrors the code. **Changes.** Over `raftCore` (from `specs-ref`'s `raft__reduceUncommittedSize.lean`, over `NState`).
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

/-- (internal) Shrinks the uncommitted-size estimate (saturating). -/
def raft.reduceUncommittedSize.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (s : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"reduceUncommittedSize")) (Val #s))
  {{ RET #(); raftCore r γ id ρ }}

end spec
end Raft
end EtcdGrove
end Perennial
