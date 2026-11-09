/-
`db.freepages()` (`db.go`): a read transaction (the spare reader slot) walks the tree; the ids below the high-water mark it does not reach, sorted. Users: `loadFreelist`, `rollback` under `NoFreelistSync`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the free ids (sorted, below the high-water mark). -/
def DB.freepages.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M ∗ ⌜M.metaOk = true⌝ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"freepages")) (Val #()))
  {{ (s : GoSlice), RET #s; dbRaw db γ M ∗ ∃ ids : List w64, s ↦* ids ∗ ⌜∀ x ∈ ids, 2 ≤ uint.nat x ∧ uint.nat x < M.hwm⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
