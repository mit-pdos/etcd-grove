/-
## `(*readOnly).AckedIndex(voterID)` (internal)

**Users**: quorum's `CommittedIndex`, through the `AckedIndexer` interface (`maybeAdvance` passes
`ro`; R4's contract, requested). Mirrors the code. **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/readOnly__AckedIndex.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) The position `id` acknowledged, if any. -/
def readOnly.AckedIndex.spec : Prop :=
  ∀ (ro : Loc) (rs : ReadOnlyState) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ readOnly ro rs }}
    (App (Val (ro @!! go.GoType.PointerType go_etcd_io.raft.v3.readOnly.ty @!! go!"AckedIndex")) (Val #id))
  {{ (idx : w64) (found : Bool), RET (PairV #idx #found); readOnly ro rs ∗
      ⌜(found = true ∧ rs.acks !! id = some idx) ∨
       (found = false ∧ rs.acks !! id = none ∧ idx = W64 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
