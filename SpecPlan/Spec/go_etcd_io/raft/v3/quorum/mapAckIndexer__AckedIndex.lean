/-
## `mapAckIndexer.AckedIndex(id)` (internal)

**Users.** None outside quorum's tests (an `AckedIndexer` over a plain map). Mirrors the code: a
lookup. **Changes.** Unchanged (from `specs-ref`'s `quorum/mapAckIndexer__AckedIndex.lean`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.quorum.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Quorum

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.quorum.Assumptions]

/-- (internal) The map's entry for `id`, if any. -/
def mapAckIndexer.AckedIndex.spec : Prop :=
  ∀ (m : GoMap) (dq : DFrac) (mm : GMap w64 w64) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ ownMap m dq mm }}
    (App (Val (m @!! go_etcd_io.raft.v3.quorum.mapAckIndexer.ty @!! go!"AckedIndex")) (Val #id))
  {{ RET (PairV #((mm !! id).getD (W64 0)) #(decide (id ∈ mm))); ownMap m dq mm }}

end spec
end Quorum
end EtcdGrove
end Perennial
