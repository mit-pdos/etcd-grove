/-
`db.grow(sz)` (`db.go`): truncates the file up to `sz` (an `AllocSize` step) and syncs unless `NoGrowSync`. Users: `Commit`.
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

/-- (internal) the file at least `sz` long, or an error (an errno; a failed sync recorded by `Commit`'s settling update). -/
def DB.grow.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM) (sz : w64),
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"grow")) (Val #sz))
  {{ (err : GoInterface), RET #err; ∃ M' : DbM, dbRaw db γ M' ∗ ⌜err = GoInterface.nil → uint.nat sz ≤ M'.fileSz⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
